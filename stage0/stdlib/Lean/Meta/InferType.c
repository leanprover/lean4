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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2341_, lean_object* v_inferType_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
uint8_t v_cacheInferType_2348_; 
v_cacheInferType_2348_ = lean_ctor_get_uint8(v_a_2343_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec_ref(v_e_2341_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
v___x_2349_ = lean_apply_5(v_inferType_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, lean_box(0));
return v___x_2349_;
}
else
{
uint8_t v___x_2350_; 
v___x_2350_ = l_Lean_Expr_hasMVar(v_e_2341_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2341_, v_a_2343_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2405_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2405_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2405_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v_cache_2357_; lean_object* v_inferType_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = lean_st_ref_get(v_a_2344_);
v_cache_2357_ = lean_ctor_get(v___x_2356_, 1);
lean_inc_ref(v_cache_2357_);
lean_dec(v___x_2356_);
v_inferType_2358_ = lean_ctor_get(v_cache_2357_, 0);
lean_inc_ref(v_inferType_2358_);
lean_dec_ref(v_cache_2357_);
v___f_2359_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0));
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1));
lean_inc(v_a_2352_);
v___x_2361_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2359_, v___x_2360_, v_inferType_2358_, v_a_2352_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2362_; 
lean_del_object(v___x_2354_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
v___x_2362_ = lean_apply_5(v_inferType_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, lean_box(0));
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; uint8_t v___x_2364_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
v___x_2364_ = l_Lean_Expr_hasMVar(v_a_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2399_; 
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2362_, 0);
lean_dec(v_unused_2400_);
v___x_2366_ = v___x_2362_;
v_isShared_2367_ = v_isSharedCheck_2399_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v___x_2362_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2399_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v_cache_2369_; lean_object* v_mctx_2370_; lean_object* v_zetaDeltaFVarIds_2371_; lean_object* v_postponed_2372_; lean_object* v_diag_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2398_; 
v___x_2368_ = lean_st_ref_take(v_a_2344_);
v_cache_2369_ = lean_ctor_get(v___x_2368_, 1);
v_mctx_2370_ = lean_ctor_get(v___x_2368_, 0);
v_zetaDeltaFVarIds_2371_ = lean_ctor_get(v___x_2368_, 2);
v_postponed_2372_ = lean_ctor_get(v___x_2368_, 3);
v_diag_2373_ = lean_ctor_get(v___x_2368_, 4);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2375_ = v___x_2368_;
v_isShared_2376_ = v_isSharedCheck_2398_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_diag_2373_);
lean_inc(v_postponed_2372_);
lean_inc(v_zetaDeltaFVarIds_2371_);
lean_inc(v_cache_2369_);
lean_inc(v_mctx_2370_);
lean_dec(v___x_2368_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2398_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v_inferType_2377_; lean_object* v_funInfo_2378_; lean_object* v_synthInstance_2379_; lean_object* v_whnf_2380_; lean_object* v_defEqTrans_2381_; lean_object* v_defEqPerm_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2397_; 
v_inferType_2377_ = lean_ctor_get(v_cache_2369_, 0);
v_funInfo_2378_ = lean_ctor_get(v_cache_2369_, 1);
v_synthInstance_2379_ = lean_ctor_get(v_cache_2369_, 2);
v_whnf_2380_ = lean_ctor_get(v_cache_2369_, 3);
v_defEqTrans_2381_ = lean_ctor_get(v_cache_2369_, 4);
v_defEqPerm_2382_ = lean_ctor_get(v_cache_2369_, 5);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_cache_2369_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2384_ = v_cache_2369_;
v_isShared_2385_ = v_isSharedCheck_2397_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_defEqPerm_2382_);
lean_inc(v_defEqTrans_2381_);
lean_inc(v_whnf_2380_);
lean_inc(v_synthInstance_2379_);
lean_inc(v_funInfo_2378_);
lean_inc(v_inferType_2377_);
lean_dec(v_cache_2369_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2397_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_inc(v_a_2363_);
v___x_2386_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2359_, v___x_2360_, v_inferType_2377_, v_a_2352_, v_a_2363_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_funInfo_2378_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_synthInstance_2379_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_whnf_2380_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_defEqTrans_2381_);
lean_ctor_set(v_reuseFailAlloc_2396_, 5, v_defEqPerm_2382_);
v___x_2388_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 1, v___x_2388_);
v___x_2390_ = v___x_2375_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_mctx_2370_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_zetaDeltaFVarIds_2371_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_postponed_2372_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_diag_2373_);
v___x_2390_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = lean_st_ref_set(v_a_2344_, v___x_2390_);
if (v_isShared_2367_ == 0)
{
v___x_2393_ = v___x_2366_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2363_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2363_);
lean_dec(v_a_2352_);
return v___x_2362_;
}
}
else
{
lean_dec(v_a_2352_);
return v___x_2362_;
}
}
else
{
lean_object* v_val_2401_; lean_object* v___x_2403_; 
lean_dec(v_a_2352_);
lean_dec_ref(v_inferType_2342_);
v_val_2401_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_val_2401_);
lean_dec_ref(v___x_2361_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v_val_2401_);
v___x_2403_ = v___x_2354_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_val_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v_inferType_2342_);
v_a_2406_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2351_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2351_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v___x_2414_; 
lean_dec_ref(v_e_2341_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
v___x_2414_ = lean_apply_5(v_inferType_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, lean_box(0));
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2415_, lean_object* v_inferType_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2415_, v_inferType_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___y_2430_; uint8_t v___y_2431_; lean_object* v___y_2432_; uint8_t v___y_2433_; lean_object* v___y_2434_; uint8_t v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; uint8_t v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; uint8_t v___y_2469_; lean_object* v___x_2527_; uint8_t v_transparency_2528_; uint8_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2527_ = l_Lean_Meta_Context_config(v_a_2424_);
v_transparency_2528_ = lean_ctor_get_uint8(v___x_2527_, 9);
lean_dec_ref(v___x_2527_);
v___x_2529_ = 1;
v___x_2530_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
v___y_2469_ = v_transparency_2528_;
goto v___jp_2468_;
}
else
{
v___y_2469_ = v___x_2529_;
goto v___jp_2468_;
}
v___jp_2429_:
{
lean_object* v___x_2441_; uint8_t v_foApprox_2442_; uint8_t v_ctxApprox_2443_; uint8_t v_quasiPatternApprox_2444_; uint8_t v_constApprox_2445_; uint8_t v_isDefEqStuckEx_2446_; uint8_t v_unificationHints_2447_; uint8_t v_proofIrrelevance_2448_; uint8_t v_assignSyntheticOpaque_2449_; uint8_t v_offsetCnstrs_2450_; uint8_t v_transparency_2451_; uint8_t v_univApprox_2452_; uint8_t v_zetaUnused_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2467_; 
v___x_2441_ = l_Lean_Meta_Context_config(v___y_2439_);
lean_dec_ref(v___y_2439_);
v_foApprox_2442_ = lean_ctor_get_uint8(v___x_2441_, 0);
v_ctxApprox_2443_ = lean_ctor_get_uint8(v___x_2441_, 1);
v_quasiPatternApprox_2444_ = lean_ctor_get_uint8(v___x_2441_, 2);
v_constApprox_2445_ = lean_ctor_get_uint8(v___x_2441_, 3);
v_isDefEqStuckEx_2446_ = lean_ctor_get_uint8(v___x_2441_, 4);
v_unificationHints_2447_ = lean_ctor_get_uint8(v___x_2441_, 5);
v_proofIrrelevance_2448_ = lean_ctor_get_uint8(v___x_2441_, 6);
v_assignSyntheticOpaque_2449_ = lean_ctor_get_uint8(v___x_2441_, 7);
v_offsetCnstrs_2450_ = lean_ctor_get_uint8(v___x_2441_, 8);
v_transparency_2451_ = lean_ctor_get_uint8(v___x_2441_, 9);
v_univApprox_2452_ = lean_ctor_get_uint8(v___x_2441_, 11);
v_zetaUnused_2453_ = lean_ctor_get_uint8(v___x_2441_, 17);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2455_ = v___x_2441_;
v_isShared_2456_ = v_isSharedCheck_2467_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v___x_2441_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2467_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
uint8_t v___x_2457_; uint8_t v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2461_; 
v___x_2457_ = 1;
v___x_2458_ = 0;
v___x_2459_ = 2;
if (v_isShared_2456_ == 0)
{
v___x_2461_ = v___x_2455_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 0, v_foApprox_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 1, v_ctxApprox_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 2, v_quasiPatternApprox_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 3, v_constApprox_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 4, v_isDefEqStuckEx_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 5, v_unificationHints_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 6, v_proofIrrelevance_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 7, v_assignSyntheticOpaque_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 8, v_offsetCnstrs_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 9, v_transparency_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 11, v_univApprox_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2466_, 17, v_zetaUnused_2453_);
v___x_2461_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
uint64_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_ctor_set_uint8(v___x_2461_, 10, v___x_2458_);
lean_ctor_set_uint8(v___x_2461_, 12, v___x_2457_);
lean_ctor_set_uint8(v___x_2461_, 13, v___x_2457_);
lean_ctor_set_uint8(v___x_2461_, 14, v___x_2459_);
lean_ctor_set_uint8(v___x_2461_, 15, v___x_2457_);
lean_ctor_set_uint8(v___x_2461_, 16, v___x_2457_);
lean_ctor_set_uint8(v___x_2461_, 18, v___x_2457_);
v___x_2462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2461_);
v___x_2463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set_uint64(v___x_2463_, sizeof(void*)*1, v___x_2462_);
lean_inc(v___y_2436_);
lean_inc(v___y_2440_);
lean_inc(v___y_2434_);
lean_inc_ref(v___y_2432_);
lean_inc_ref(v___y_2437_);
lean_inc(v___y_2430_);
v___x_2464_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___y_2430_);
lean_ctor_set(v___x_2464_, 2, v___y_2437_);
lean_ctor_set(v___x_2464_, 3, v___y_2432_);
lean_ctor_set(v___x_2464_, 4, v___y_2434_);
lean_ctor_set(v___x_2464_, 5, v___y_2440_);
lean_ctor_set(v___x_2464_, 6, v___y_2436_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*7, v___y_2435_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*7 + 1, v___y_2438_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*7 + 2, v___y_2433_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*7 + 3, v___y_2431_);
lean_inc(v_a_2427_);
lean_inc_ref(v_a_2426_);
lean_inc(v_a_2425_);
v___x_2465_ = lean_apply_5(v_x_2423_, v___x_2464_, v_a_2425_, v_a_2426_, v_a_2427_, lean_box(0));
return v___x_2465_;
}
}
}
v___jp_2468_:
{
lean_object* v___x_2470_; uint8_t v_foApprox_2471_; uint8_t v_ctxApprox_2472_; uint8_t v_quasiPatternApprox_2473_; uint8_t v_constApprox_2474_; uint8_t v_isDefEqStuckEx_2475_; uint8_t v_unificationHints_2476_; uint8_t v_proofIrrelevance_2477_; uint8_t v_assignSyntheticOpaque_2478_; uint8_t v_offsetCnstrs_2479_; uint8_t v_etaStruct_2480_; uint8_t v_univApprox_2481_; uint8_t v_iota_2482_; uint8_t v_beta_2483_; uint8_t v_proj_2484_; uint8_t v_zeta_2485_; uint8_t v_zetaDelta_2486_; uint8_t v_zetaUnused_2487_; uint8_t v_zetaHave_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2526_; 
v___x_2470_ = l_Lean_Meta_Context_config(v_a_2424_);
v_foApprox_2471_ = lean_ctor_get_uint8(v___x_2470_, 0);
v_ctxApprox_2472_ = lean_ctor_get_uint8(v___x_2470_, 1);
v_quasiPatternApprox_2473_ = lean_ctor_get_uint8(v___x_2470_, 2);
v_constApprox_2474_ = lean_ctor_get_uint8(v___x_2470_, 3);
v_isDefEqStuckEx_2475_ = lean_ctor_get_uint8(v___x_2470_, 4);
v_unificationHints_2476_ = lean_ctor_get_uint8(v___x_2470_, 5);
v_proofIrrelevance_2477_ = lean_ctor_get_uint8(v___x_2470_, 6);
v_assignSyntheticOpaque_2478_ = lean_ctor_get_uint8(v___x_2470_, 7);
v_offsetCnstrs_2479_ = lean_ctor_get_uint8(v___x_2470_, 8);
v_etaStruct_2480_ = lean_ctor_get_uint8(v___x_2470_, 10);
v_univApprox_2481_ = lean_ctor_get_uint8(v___x_2470_, 11);
v_iota_2482_ = lean_ctor_get_uint8(v___x_2470_, 12);
v_beta_2483_ = lean_ctor_get_uint8(v___x_2470_, 13);
v_proj_2484_ = lean_ctor_get_uint8(v___x_2470_, 14);
v_zeta_2485_ = lean_ctor_get_uint8(v___x_2470_, 15);
v_zetaDelta_2486_ = lean_ctor_get_uint8(v___x_2470_, 16);
v_zetaUnused_2487_ = lean_ctor_get_uint8(v___x_2470_, 17);
v_zetaHave_2488_ = lean_ctor_get_uint8(v___x_2470_, 18);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2490_ = v___x_2470_;
v_isShared_2491_ = v_isSharedCheck_2526_;
goto v_resetjp_2489_;
}
else
{
lean_dec(v___x_2470_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2526_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
uint8_t v_trackZetaDelta_2492_; lean_object* v_zetaDeltaSet_2493_; lean_object* v_lctx_2494_; lean_object* v_localInstances_2495_; lean_object* v_defEqCtx_x3f_2496_; lean_object* v_synthPendingDepth_2497_; lean_object* v_canUnfold_x3f_2498_; uint8_t v_univApprox_2499_; uint8_t v_inTypeClassResolution_2500_; uint8_t v_cacheInferType_2501_; lean_object* v_config_2503_; 
v_trackZetaDelta_2492_ = lean_ctor_get_uint8(v_a_2424_, sizeof(void*)*7);
v_zetaDeltaSet_2493_ = lean_ctor_get(v_a_2424_, 1);
v_lctx_2494_ = lean_ctor_get(v_a_2424_, 2);
v_localInstances_2495_ = lean_ctor_get(v_a_2424_, 3);
v_defEqCtx_x3f_2496_ = lean_ctor_get(v_a_2424_, 4);
v_synthPendingDepth_2497_ = lean_ctor_get(v_a_2424_, 5);
v_canUnfold_x3f_2498_ = lean_ctor_get(v_a_2424_, 6);
v_univApprox_2499_ = lean_ctor_get_uint8(v_a_2424_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2500_ = lean_ctor_get_uint8(v_a_2424_, sizeof(void*)*7 + 2);
v_cacheInferType_2501_ = lean_ctor_get_uint8(v_a_2424_, sizeof(void*)*7 + 3);
if (v_isShared_2491_ == 0)
{
v_config_2503_ = v___x_2490_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 0, v_foApprox_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 1, v_ctxApprox_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 2, v_quasiPatternApprox_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 3, v_constApprox_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 4, v_isDefEqStuckEx_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 5, v_unificationHints_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 6, v_proofIrrelevance_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 7, v_assignSyntheticOpaque_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 8, v_offsetCnstrs_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 10, v_etaStruct_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 11, v_univApprox_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 12, v_iota_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 13, v_beta_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 14, v_proj_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 15, v_zeta_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 16, v_zetaDelta_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 17, v_zetaUnused_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, 18, v_zetaHave_2488_);
v_config_2503_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v_key_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v_beta_2513_; 
lean_ctor_set_uint8(v_config_2503_, 9, v___y_2469_);
v___x_2504_ = l_Lean_Meta_Context_configKey(v_a_2424_);
v___x_2505_ = 2ULL;
v___x_2506_ = lean_uint64_shift_right(v___x_2504_, v___x_2505_);
v___x_2507_ = lean_uint64_shift_left(v___x_2506_, v___x_2505_);
v___x_2508_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2469_);
v_key_2509_ = lean_uint64_lor(v___x_2507_, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2510_, 0, v_config_2503_);
lean_ctor_set_uint64(v___x_2510_, sizeof(void*)*1, v_key_2509_);
lean_inc(v_canUnfold_x3f_2498_);
lean_inc(v_synthPendingDepth_2497_);
lean_inc(v_defEqCtx_x3f_2496_);
lean_inc_ref(v_localInstances_2495_);
lean_inc_ref(v_lctx_2494_);
lean_inc(v_zetaDeltaSet_2493_);
v___x_2511_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v_zetaDeltaSet_2493_);
lean_ctor_set(v___x_2511_, 2, v_lctx_2494_);
lean_ctor_set(v___x_2511_, 3, v_localInstances_2495_);
lean_ctor_set(v___x_2511_, 4, v_defEqCtx_x3f_2496_);
lean_ctor_set(v___x_2511_, 5, v_synthPendingDepth_2497_);
lean_ctor_set(v___x_2511_, 6, v_canUnfold_x3f_2498_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*7, v_trackZetaDelta_2492_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*7 + 1, v_univApprox_2499_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2500_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*7 + 3, v_cacheInferType_2501_);
v___x_2512_ = l_Lean_Meta_Context_config(v___x_2511_);
v_beta_2513_ = lean_ctor_get_uint8(v___x_2512_, 13);
if (v_beta_2513_ == 0)
{
lean_dec_ref(v___x_2512_);
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
uint8_t v_iota_2514_; 
v_iota_2514_ = lean_ctor_get_uint8(v___x_2512_, 12);
if (v_iota_2514_ == 0)
{
lean_dec_ref(v___x_2512_);
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
uint8_t v_zeta_2515_; 
v_zeta_2515_ = lean_ctor_get_uint8(v___x_2512_, 15);
if (v_zeta_2515_ == 0)
{
lean_dec_ref(v___x_2512_);
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
uint8_t v_zetaHave_2516_; 
v_zetaHave_2516_ = lean_ctor_get_uint8(v___x_2512_, 18);
if (v_zetaHave_2516_ == 0)
{
lean_dec_ref(v___x_2512_);
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
uint8_t v_zetaDelta_2517_; 
v_zetaDelta_2517_ = lean_ctor_get_uint8(v___x_2512_, 16);
if (v_zetaDelta_2517_ == 0)
{
lean_dec_ref(v___x_2512_);
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
uint8_t v_etaStruct_2518_; uint8_t v_proj_2519_; uint8_t v___x_2520_; uint8_t v___x_2521_; 
v_etaStruct_2518_ = lean_ctor_get_uint8(v___x_2512_, 10);
v_proj_2519_ = lean_ctor_get_uint8(v___x_2512_, 14);
lean_dec_ref(v___x_2512_);
v___x_2520_ = 2;
v___x_2521_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
uint8_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = 0;
v___x_2523_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2518_, v___x_2522_);
if (v___x_2523_ == 0)
{
v___y_2430_ = v_zetaDeltaSet_2493_;
v___y_2431_ = v_cacheInferType_2501_;
v___y_2432_ = v_localInstances_2495_;
v___y_2433_ = v_inTypeClassResolution_2500_;
v___y_2434_ = v_defEqCtx_x3f_2496_;
v___y_2435_ = v_trackZetaDelta_2492_;
v___y_2436_ = v_canUnfold_x3f_2498_;
v___y_2437_ = v_lctx_2494_;
v___y_2438_ = v_univApprox_2499_;
v___y_2439_ = v___x_2511_;
v___y_2440_ = v_synthPendingDepth_2497_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2524_; 
lean_inc(v_a_2427_);
lean_inc_ref(v_a_2426_);
lean_inc(v_a_2425_);
v___x_2524_ = lean_apply_5(v_x_2423_, v___x_2511_, v_a_2425_, v_a_2426_, v_a_2427_, lean_box(0));
return v___x_2524_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2538_, lean_object* v_x_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___y_2546_; uint8_t v___y_2547_; lean_object* v___y_2548_; uint8_t v___y_2549_; lean_object* v___y_2550_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; uint8_t v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; uint8_t v___y_2585_; lean_object* v___x_2643_; uint8_t v_transparency_2644_; uint8_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2643_ = l_Lean_Meta_Context_config(v_a_2540_);
v_transparency_2644_ = lean_ctor_get_uint8(v___x_2643_, 9);
lean_dec_ref(v___x_2643_);
v___x_2645_ = 1;
v___x_2646_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
v___y_2585_ = v_transparency_2644_;
goto v___jp_2584_;
}
else
{
v___y_2585_ = v___x_2645_;
goto v___jp_2584_;
}
v___jp_2545_:
{
lean_object* v___x_2557_; uint8_t v_foApprox_2558_; uint8_t v_ctxApprox_2559_; uint8_t v_quasiPatternApprox_2560_; uint8_t v_constApprox_2561_; uint8_t v_isDefEqStuckEx_2562_; uint8_t v_unificationHints_2563_; uint8_t v_proofIrrelevance_2564_; uint8_t v_assignSyntheticOpaque_2565_; uint8_t v_offsetCnstrs_2566_; uint8_t v_transparency_2567_; uint8_t v_univApprox_2568_; uint8_t v_zetaUnused_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2583_; 
v___x_2557_ = l_Lean_Meta_Context_config(v___y_2555_);
lean_dec_ref(v___y_2555_);
v_foApprox_2558_ = lean_ctor_get_uint8(v___x_2557_, 0);
v_ctxApprox_2559_ = lean_ctor_get_uint8(v___x_2557_, 1);
v_quasiPatternApprox_2560_ = lean_ctor_get_uint8(v___x_2557_, 2);
v_constApprox_2561_ = lean_ctor_get_uint8(v___x_2557_, 3);
v_isDefEqStuckEx_2562_ = lean_ctor_get_uint8(v___x_2557_, 4);
v_unificationHints_2563_ = lean_ctor_get_uint8(v___x_2557_, 5);
v_proofIrrelevance_2564_ = lean_ctor_get_uint8(v___x_2557_, 6);
v_assignSyntheticOpaque_2565_ = lean_ctor_get_uint8(v___x_2557_, 7);
v_offsetCnstrs_2566_ = lean_ctor_get_uint8(v___x_2557_, 8);
v_transparency_2567_ = lean_ctor_get_uint8(v___x_2557_, 9);
v_univApprox_2568_ = lean_ctor_get_uint8(v___x_2557_, 11);
v_zetaUnused_2569_ = lean_ctor_get_uint8(v___x_2557_, 17);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2571_ = v___x_2557_;
v_isShared_2572_ = v_isSharedCheck_2583_;
goto v_resetjp_2570_;
}
else
{
lean_dec(v___x_2557_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2583_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
uint8_t v___x_2573_; uint8_t v___x_2574_; uint8_t v___x_2575_; lean_object* v___x_2577_; 
v___x_2573_ = 1;
v___x_2574_ = 0;
v___x_2575_ = 2;
if (v_isShared_2572_ == 0)
{
v___x_2577_ = v___x_2571_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 0, v_foApprox_2558_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 1, v_ctxApprox_2559_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 2, v_quasiPatternApprox_2560_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 3, v_constApprox_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 4, v_isDefEqStuckEx_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 5, v_unificationHints_2563_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 6, v_proofIrrelevance_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 7, v_assignSyntheticOpaque_2565_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 8, v_offsetCnstrs_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 9, v_transparency_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 11, v_univApprox_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2582_, 17, v_zetaUnused_2569_);
v___x_2577_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
uint64_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_ctor_set_uint8(v___x_2577_, 10, v___x_2574_);
lean_ctor_set_uint8(v___x_2577_, 12, v___x_2573_);
lean_ctor_set_uint8(v___x_2577_, 13, v___x_2573_);
lean_ctor_set_uint8(v___x_2577_, 14, v___x_2575_);
lean_ctor_set_uint8(v___x_2577_, 15, v___x_2573_);
lean_ctor_set_uint8(v___x_2577_, 16, v___x_2573_);
lean_ctor_set_uint8(v___x_2577_, 18, v___x_2573_);
v___x_2578_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2577_);
v___x_2579_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set_uint64(v___x_2579_, sizeof(void*)*1, v___x_2578_);
lean_inc(v___y_2552_);
lean_inc(v___y_2556_);
lean_inc(v___y_2550_);
lean_inc_ref(v___y_2548_);
lean_inc_ref(v___y_2553_);
lean_inc(v___y_2546_);
v___x_2580_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___y_2546_);
lean_ctor_set(v___x_2580_, 2, v___y_2553_);
lean_ctor_set(v___x_2580_, 3, v___y_2548_);
lean_ctor_set(v___x_2580_, 4, v___y_2550_);
lean_ctor_set(v___x_2580_, 5, v___y_2556_);
lean_ctor_set(v___x_2580_, 6, v___y_2552_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*7, v___y_2551_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*7 + 1, v___y_2554_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*7 + 2, v___y_2549_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*7 + 3, v___y_2547_);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
lean_inc(v_a_2541_);
v___x_2581_ = lean_apply_5(v_x_2539_, v___x_2580_, v_a_2541_, v_a_2542_, v_a_2543_, lean_box(0));
return v___x_2581_;
}
}
}
v___jp_2584_:
{
lean_object* v___x_2586_; uint8_t v_foApprox_2587_; uint8_t v_ctxApprox_2588_; uint8_t v_quasiPatternApprox_2589_; uint8_t v_constApprox_2590_; uint8_t v_isDefEqStuckEx_2591_; uint8_t v_unificationHints_2592_; uint8_t v_proofIrrelevance_2593_; uint8_t v_assignSyntheticOpaque_2594_; uint8_t v_offsetCnstrs_2595_; uint8_t v_etaStruct_2596_; uint8_t v_univApprox_2597_; uint8_t v_iota_2598_; uint8_t v_beta_2599_; uint8_t v_proj_2600_; uint8_t v_zeta_2601_; uint8_t v_zetaDelta_2602_; uint8_t v_zetaUnused_2603_; uint8_t v_zetaHave_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2642_; 
v___x_2586_ = l_Lean_Meta_Context_config(v_a_2540_);
v_foApprox_2587_ = lean_ctor_get_uint8(v___x_2586_, 0);
v_ctxApprox_2588_ = lean_ctor_get_uint8(v___x_2586_, 1);
v_quasiPatternApprox_2589_ = lean_ctor_get_uint8(v___x_2586_, 2);
v_constApprox_2590_ = lean_ctor_get_uint8(v___x_2586_, 3);
v_isDefEqStuckEx_2591_ = lean_ctor_get_uint8(v___x_2586_, 4);
v_unificationHints_2592_ = lean_ctor_get_uint8(v___x_2586_, 5);
v_proofIrrelevance_2593_ = lean_ctor_get_uint8(v___x_2586_, 6);
v_assignSyntheticOpaque_2594_ = lean_ctor_get_uint8(v___x_2586_, 7);
v_offsetCnstrs_2595_ = lean_ctor_get_uint8(v___x_2586_, 8);
v_etaStruct_2596_ = lean_ctor_get_uint8(v___x_2586_, 10);
v_univApprox_2597_ = lean_ctor_get_uint8(v___x_2586_, 11);
v_iota_2598_ = lean_ctor_get_uint8(v___x_2586_, 12);
v_beta_2599_ = lean_ctor_get_uint8(v___x_2586_, 13);
v_proj_2600_ = lean_ctor_get_uint8(v___x_2586_, 14);
v_zeta_2601_ = lean_ctor_get_uint8(v___x_2586_, 15);
v_zetaDelta_2602_ = lean_ctor_get_uint8(v___x_2586_, 16);
v_zetaUnused_2603_ = lean_ctor_get_uint8(v___x_2586_, 17);
v_zetaHave_2604_ = lean_ctor_get_uint8(v___x_2586_, 18);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2606_ = v___x_2586_;
v_isShared_2607_ = v_isSharedCheck_2642_;
goto v_resetjp_2605_;
}
else
{
lean_dec(v___x_2586_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2642_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
uint8_t v_trackZetaDelta_2608_; lean_object* v_zetaDeltaSet_2609_; lean_object* v_lctx_2610_; lean_object* v_localInstances_2611_; lean_object* v_defEqCtx_x3f_2612_; lean_object* v_synthPendingDepth_2613_; lean_object* v_canUnfold_x3f_2614_; uint8_t v_univApprox_2615_; uint8_t v_inTypeClassResolution_2616_; uint8_t v_cacheInferType_2617_; lean_object* v_config_2619_; 
v_trackZetaDelta_2608_ = lean_ctor_get_uint8(v_a_2540_, sizeof(void*)*7);
v_zetaDeltaSet_2609_ = lean_ctor_get(v_a_2540_, 1);
v_lctx_2610_ = lean_ctor_get(v_a_2540_, 2);
v_localInstances_2611_ = lean_ctor_get(v_a_2540_, 3);
v_defEqCtx_x3f_2612_ = lean_ctor_get(v_a_2540_, 4);
v_synthPendingDepth_2613_ = lean_ctor_get(v_a_2540_, 5);
v_canUnfold_x3f_2614_ = lean_ctor_get(v_a_2540_, 6);
v_univApprox_2615_ = lean_ctor_get_uint8(v_a_2540_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2616_ = lean_ctor_get_uint8(v_a_2540_, sizeof(void*)*7 + 2);
v_cacheInferType_2617_ = lean_ctor_get_uint8(v_a_2540_, sizeof(void*)*7 + 3);
if (v_isShared_2607_ == 0)
{
v_config_2619_ = v___x_2606_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 0, v_foApprox_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 1, v_ctxApprox_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 2, v_quasiPatternApprox_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 3, v_constApprox_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 4, v_isDefEqStuckEx_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 5, v_unificationHints_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 6, v_proofIrrelevance_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 7, v_assignSyntheticOpaque_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 8, v_offsetCnstrs_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 10, v_etaStruct_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 11, v_univApprox_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 12, v_iota_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 13, v_beta_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 14, v_proj_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 15, v_zeta_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 16, v_zetaDelta_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 17, v_zetaUnused_2603_);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 18, v_zetaHave_2604_);
v_config_2619_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
uint64_t v___x_2620_; uint64_t v___x_2621_; uint64_t v___x_2622_; uint64_t v___x_2623_; uint64_t v___x_2624_; uint64_t v_key_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v_beta_2629_; 
lean_ctor_set_uint8(v_config_2619_, 9, v___y_2585_);
v___x_2620_ = l_Lean_Meta_Context_configKey(v_a_2540_);
v___x_2621_ = 2ULL;
v___x_2622_ = lean_uint64_shift_right(v___x_2620_, v___x_2621_);
v___x_2623_ = lean_uint64_shift_left(v___x_2622_, v___x_2621_);
v___x_2624_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2585_);
v_key_2625_ = lean_uint64_lor(v___x_2623_, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2626_, 0, v_config_2619_);
lean_ctor_set_uint64(v___x_2626_, sizeof(void*)*1, v_key_2625_);
lean_inc(v_canUnfold_x3f_2614_);
lean_inc(v_synthPendingDepth_2613_);
lean_inc(v_defEqCtx_x3f_2612_);
lean_inc_ref(v_localInstances_2611_);
lean_inc_ref(v_lctx_2610_);
lean_inc(v_zetaDeltaSet_2609_);
v___x_2627_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v_zetaDeltaSet_2609_);
lean_ctor_set(v___x_2627_, 2, v_lctx_2610_);
lean_ctor_set(v___x_2627_, 3, v_localInstances_2611_);
lean_ctor_set(v___x_2627_, 4, v_defEqCtx_x3f_2612_);
lean_ctor_set(v___x_2627_, 5, v_synthPendingDepth_2613_);
lean_ctor_set(v___x_2627_, 6, v_canUnfold_x3f_2614_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*7, v_trackZetaDelta_2608_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*7 + 1, v_univApprox_2615_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2616_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*7 + 3, v_cacheInferType_2617_);
v___x_2628_ = l_Lean_Meta_Context_config(v___x_2627_);
v_beta_2629_ = lean_ctor_get_uint8(v___x_2628_, 13);
if (v_beta_2629_ == 0)
{
lean_dec_ref(v___x_2628_);
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
uint8_t v_iota_2630_; 
v_iota_2630_ = lean_ctor_get_uint8(v___x_2628_, 12);
if (v_iota_2630_ == 0)
{
lean_dec_ref(v___x_2628_);
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
uint8_t v_zeta_2631_; 
v_zeta_2631_ = lean_ctor_get_uint8(v___x_2628_, 15);
if (v_zeta_2631_ == 0)
{
lean_dec_ref(v___x_2628_);
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
uint8_t v_zetaHave_2632_; 
v_zetaHave_2632_ = lean_ctor_get_uint8(v___x_2628_, 18);
if (v_zetaHave_2632_ == 0)
{
lean_dec_ref(v___x_2628_);
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
uint8_t v_zetaDelta_2633_; 
v_zetaDelta_2633_ = lean_ctor_get_uint8(v___x_2628_, 16);
if (v_zetaDelta_2633_ == 0)
{
lean_dec_ref(v___x_2628_);
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
uint8_t v_etaStruct_2634_; uint8_t v_proj_2635_; uint8_t v___x_2636_; uint8_t v___x_2637_; 
v_etaStruct_2634_ = lean_ctor_get_uint8(v___x_2628_, 10);
v_proj_2635_ = lean_ctor_get_uint8(v___x_2628_, 14);
lean_dec_ref(v___x_2628_);
v___x_2636_ = 2;
v___x_2637_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
uint8_t v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = 0;
v___x_2639_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2634_, v___x_2638_);
if (v___x_2639_ == 0)
{
v___y_2546_ = v_zetaDeltaSet_2609_;
v___y_2547_ = v_cacheInferType_2617_;
v___y_2548_ = v_localInstances_2611_;
v___y_2549_ = v_inTypeClassResolution_2616_;
v___y_2550_ = v_defEqCtx_x3f_2612_;
v___y_2551_ = v_trackZetaDelta_2608_;
v___y_2552_ = v_canUnfold_x3f_2614_;
v___y_2553_ = v_lctx_2610_;
v___y_2554_ = v_univApprox_2615_;
v___y_2555_ = v___x_2627_;
v___y_2556_ = v_synthPendingDepth_2613_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2640_; 
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
lean_inc(v_a_2541_);
v___x_2640_ = lean_apply_5(v_x_2539_, v___x_2627_, v_a_2541_, v_a_2542_, v_a_2543_, lean_box(0));
return v___x_2640_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_x_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2647_, v_x_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_){
_start:
{
lean_object* v_ks_2659_; lean_object* v_vs_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2689_; 
v_ks_2659_ = lean_ctor_get(v_x_2655_, 0);
v_vs_2660_ = lean_ctor_get(v_x_2655_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_x_2655_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2662_ = v_x_2655_;
v_isShared_2663_ = v_isSharedCheck_2689_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_vs_2660_);
lean_inc(v_ks_2659_);
lean_dec(v_x_2655_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2689_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v___y_2665_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = lean_array_get_size(v_ks_2659_);
v___x_2678_ = lean_nat_dec_lt(v_x_2656_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_del_object(v___x_2662_);
lean_dec(v_x_2656_);
v___x_2679_ = lean_array_push(v_ks_2659_, v_x_2657_);
v___x_2680_ = lean_array_push(v_vs_2660_, v_x_2658_);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
return v___x_2681_;
}
else
{
lean_object* v_expr_2682_; uint64_t v_configKey_2683_; lean_object* v_k_x27_2684_; lean_object* v_expr_2685_; uint64_t v_configKey_2686_; uint8_t v___x_2687_; 
v_expr_2682_ = lean_ctor_get(v_x_2657_, 0);
v_configKey_2683_ = lean_ctor_get_uint64(v_x_2657_, sizeof(void*)*1);
v_k_x27_2684_ = lean_array_fget_borrowed(v_ks_2659_, v_x_2656_);
v_expr_2685_ = lean_ctor_get(v_k_x27_2684_, 0);
v_configKey_2686_ = lean_ctor_get_uint64(v_k_x27_2684_, sizeof(void*)*1);
v___x_2687_ = lean_expr_equal(v_expr_2682_, v_expr_2685_);
if (v___x_2687_ == 0)
{
v___y_2665_ = v___x_2687_;
goto v___jp_2664_;
}
else
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_uint64_dec_eq(v_configKey_2683_, v_configKey_2686_);
v___y_2665_ = v___x_2688_;
goto v___jp_2664_;
}
}
v___jp_2664_:
{
if (v___y_2665_ == 0)
{
lean_object* v___x_2667_; 
if (v_isShared_2663_ == 0)
{
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_ks_2659_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_vs_2660_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_add(v_x_2656_, v___x_2668_);
lean_dec(v_x_2656_);
v_x_2655_ = v___x_2667_;
v_x_2656_ = v___x_2669_;
goto _start;
}
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2672_ = lean_array_fset(v_ks_2659_, v_x_2656_, v_x_2657_);
v___x_2673_ = lean_array_fset(v_vs_2660_, v_x_2656_, v_x_2658_);
lean_dec(v_x_2656_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2673_);
lean_ctor_set(v___x_2662_, 0, v___x_2672_);
v___x_2675_ = v___x_2662_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(lean_object* v_n_2690_, lean_object* v_k_2691_, lean_object* v_v_2692_){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2690_, v___x_2693_, v_k_2691_, v_v_2692_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object* v_x_2696_, size_t v_x_2697_, size_t v_x_2698_, lean_object* v_x_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2696_) == 0)
{
lean_object* v_es_2701_; size_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; lean_object* v_j_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v_es_2701_ = lean_ctor_get(v_x_2696_, 0);
v___x_2702_ = ((size_t)5ULL);
v___x_2703_ = ((size_t)1ULL);
v___x_2704_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2705_ = lean_usize_land(v_x_2697_, v___x_2704_);
v_j_2706_ = lean_usize_to_nat(v___x_2705_);
v___x_2707_ = lean_array_get_size(v_es_2701_);
v___x_2708_ = lean_nat_dec_lt(v_j_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_dec(v_j_2706_);
lean_dec(v_x_2700_);
lean_dec_ref(v_x_2699_);
return v_x_2696_;
}
else
{
lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2752_; 
lean_inc_ref(v_es_2701_);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_x_2696_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; 
v_unused_2753_ = lean_ctor_get(v_x_2696_, 0);
lean_dec(v_unused_2753_);
v___x_2710_ = v_x_2696_;
v_isShared_2711_ = v_isSharedCheck_2752_;
goto v_resetjp_2709_;
}
else
{
lean_dec(v_x_2696_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2752_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v_v_2712_; lean_object* v___x_2713_; lean_object* v_xs_x27_2714_; lean_object* v___y_2716_; 
v_v_2712_ = lean_array_fget(v_es_2701_, v_j_2706_);
v___x_2713_ = lean_box(0);
v_xs_x27_2714_ = lean_array_fset(v_es_2701_, v_j_2706_, v___x_2713_);
switch(lean_obj_tag(v_v_2712_))
{
case 0:
{
lean_object* v_key_2721_; lean_object* v_val_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2739_; 
v_key_2721_ = lean_ctor_get(v_v_2712_, 0);
v_val_2722_ = lean_ctor_get(v_v_2712_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_v_2712_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2724_ = v_v_2712_;
v_isShared_2725_ = v_isSharedCheck_2739_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_val_2722_);
lean_inc(v_key_2721_);
lean_dec(v_v_2712_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2739_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint8_t v___y_2727_; lean_object* v_expr_2733_; uint64_t v_configKey_2734_; lean_object* v_expr_2735_; uint64_t v_configKey_2736_; uint8_t v___x_2737_; 
v_expr_2733_ = lean_ctor_get(v_x_2699_, 0);
v_configKey_2734_ = lean_ctor_get_uint64(v_x_2699_, sizeof(void*)*1);
v_expr_2735_ = lean_ctor_get(v_key_2721_, 0);
v_configKey_2736_ = lean_ctor_get_uint64(v_key_2721_, sizeof(void*)*1);
v___x_2737_ = lean_expr_equal(v_expr_2733_, v_expr_2735_);
if (v___x_2737_ == 0)
{
v___y_2727_ = v___x_2737_;
goto v___jp_2726_;
}
else
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_uint64_dec_eq(v_configKey_2734_, v_configKey_2736_);
v___y_2727_ = v___x_2738_;
goto v___jp_2726_;
}
v___jp_2726_:
{
if (v___y_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_del_object(v___x_2724_);
v___x_2728_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2721_, v_val_2722_, v_x_2699_, v_x_2700_);
v___x_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
v___y_2716_ = v___x_2729_;
goto v___jp_2715_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v_val_2722_);
lean_dec(v_key_2721_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v_x_2700_);
lean_ctor_set(v___x_2724_, 0, v_x_2699_);
v___x_2731_ = v___x_2724_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_x_2699_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_x_2700_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
v___y_2716_ = v___x_2731_;
goto v___jp_2715_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2750_; 
v_node_2740_ = lean_ctor_get(v_v_2712_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_v_2712_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2742_ = v_v_2712_;
v_isShared_2743_ = v_isSharedCheck_2750_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_node_2740_);
lean_dec(v_v_2712_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2750_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
size_t v___x_2744_; size_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2744_ = lean_usize_shift_right(v_x_2697_, v___x_2702_);
v___x_2745_ = lean_usize_add(v_x_2698_, v___x_2703_);
v___x_2746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_node_2740_, v___x_2744_, v___x_2745_, v_x_2699_, v_x_2700_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2746_);
v___x_2748_ = v___x_2742_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
v___y_2716_ = v___x_2748_;
goto v___jp_2715_;
}
}
}
default: 
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_x_2699_);
lean_ctor_set(v___x_2751_, 1, v_x_2700_);
v___y_2716_ = v___x_2751_;
goto v___jp_2715_;
}
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_array_fset(v_xs_x27_2714_, v_j_2706_, v___y_2716_);
lean_dec(v_j_2706_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2717_);
v___x_2719_ = v___x_2710_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
else
{
lean_object* v_ks_2754_; lean_object* v_vs_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2775_; 
v_ks_2754_ = lean_ctor_get(v_x_2696_, 0);
v_vs_2755_ = lean_ctor_get(v_x_2696_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_x_2696_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2757_ = v_x_2696_;
v_isShared_2758_ = v_isSharedCheck_2775_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_vs_2755_);
lean_inc(v_ks_2754_);
lean_dec(v_x_2696_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2775_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_ks_2754_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_vs_2755_);
v___x_2760_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v_newNode_2761_; uint8_t v___y_2763_; size_t v___x_2769_; uint8_t v___x_2770_; 
v_newNode_2761_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v___x_2760_, v_x_2699_, v_x_2700_);
v___x_2769_ = ((size_t)7ULL);
v___x_2770_ = lean_usize_dec_le(v___x_2769_, v_x_2698_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2771_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2761_);
v___x_2772_ = lean_unsigned_to_nat(4u);
v___x_2773_ = lean_nat_dec_lt(v___x_2771_, v___x_2772_);
lean_dec(v___x_2771_);
v___y_2763_ = v___x_2773_;
goto v___jp_2762_;
}
else
{
v___y_2763_ = v___x_2770_;
goto v___jp_2762_;
}
v___jp_2762_:
{
if (v___y_2763_ == 0)
{
lean_object* v_ks_2764_; lean_object* v_vs_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_ks_2764_ = lean_ctor_get(v_newNode_2761_, 0);
lean_inc_ref(v_ks_2764_);
v_vs_2765_ = lean_ctor_get(v_newNode_2761_, 1);
lean_inc_ref(v_vs_2765_);
lean_dec_ref(v_newNode_2761_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0);
v___x_2768_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_x_2698_, v_ks_2764_, v_vs_2765_, v___x_2766_, v___x_2767_);
lean_dec_ref(v_vs_2765_);
lean_dec_ref(v_ks_2764_);
return v___x_2768_;
}
else
{
return v_newNode_2761_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(size_t v_depth_2776_, lean_object* v_keys_2777_, lean_object* v_vals_2778_, lean_object* v_i_2779_, lean_object* v_entries_2780_){
_start:
{
lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = lean_array_get_size(v_keys_2777_);
v___x_2782_ = lean_nat_dec_lt(v_i_2779_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_dec(v_i_2779_);
return v_entries_2780_;
}
else
{
lean_object* v_k_2783_; lean_object* v_expr_2784_; uint64_t v_configKey_2785_; lean_object* v_v_2786_; uint64_t v___x_2787_; uint64_t v___x_2788_; size_t v_h_2789_; size_t v___x_2790_; lean_object* v___x_2791_; size_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v_h_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_k_2783_ = lean_array_fget_borrowed(v_keys_2777_, v_i_2779_);
v_expr_2784_ = lean_ctor_get(v_k_2783_, 0);
v_configKey_2785_ = lean_ctor_get_uint64(v_k_2783_, sizeof(void*)*1);
v_v_2786_ = lean_array_fget_borrowed(v_vals_2778_, v_i_2779_);
v___x_2787_ = l_Lean_Expr_hash(v_expr_2784_);
v___x_2788_ = lean_uint64_mix_hash(v___x_2787_, v_configKey_2785_);
v_h_2789_ = lean_uint64_to_usize(v___x_2788_);
v___x_2790_ = ((size_t)5ULL);
v___x_2791_ = lean_unsigned_to_nat(1u);
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_sub(v_depth_2776_, v___x_2792_);
v___x_2794_ = lean_usize_mul(v___x_2790_, v___x_2793_);
v_h_2795_ = lean_usize_shift_right(v_h_2789_, v___x_2794_);
v___x_2796_ = lean_nat_add(v_i_2779_, v___x_2791_);
lean_dec(v_i_2779_);
lean_inc(v_v_2786_);
lean_inc(v_k_2783_);
v___x_2797_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_entries_2780_, v_h_2795_, v_depth_2776_, v_k_2783_, v_v_2786_);
v_i_2779_ = v___x_2796_;
v_entries_2780_ = v___x_2797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_2799_, lean_object* v_keys_2800_, lean_object* v_vals_2801_, lean_object* v_i_2802_, lean_object* v_entries_2803_){
_start:
{
size_t v_depth_boxed_2804_; lean_object* v_res_2805_; 
v_depth_boxed_2804_ = lean_unbox_usize(v_depth_2799_);
lean_dec(v_depth_2799_);
v_res_2805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2804_, v_keys_2800_, v_vals_2801_, v_i_2802_, v_entries_2803_);
lean_dec_ref(v_vals_2801_);
lean_dec_ref(v_keys_2800_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object* v_x_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
size_t v_x_2105__boxed_2811_; size_t v_x_2106__boxed_2812_; lean_object* v_res_2813_; 
v_x_2105__boxed_2811_ = lean_unbox_usize(v_x_2807_);
lean_dec(v_x_2807_);
v_x_2106__boxed_2812_ = lean_unbox_usize(v_x_2808_);
lean_dec(v_x_2808_);
v_res_2813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2806_, v_x_2105__boxed_2811_, v_x_2106__boxed_2812_, v_x_2809_, v_x_2810_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v_expr_2817_; uint64_t v_configKey_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; size_t v___x_2821_; size_t v___x_2822_; lean_object* v___x_2823_; 
v_expr_2817_ = lean_ctor_get(v_x_2815_, 0);
v_configKey_2818_ = lean_ctor_get_uint64(v_x_2815_, sizeof(void*)*1);
v___x_2819_ = l_Lean_Expr_hash(v_expr_2817_);
v___x_2820_ = lean_uint64_mix_hash(v___x_2819_, v_configKey_2818_);
v___x_2821_ = lean_uint64_to_usize(v___x_2820_);
v___x_2822_ = ((size_t)1ULL);
v___x_2823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2814_, v___x_2821_, v___x_2822_, v_x_2815_, v_x_2816_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2824_, lean_object* v_vals_2825_, lean_object* v_i_2826_, lean_object* v_k_2827_){
_start:
{
uint8_t v___y_2829_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = lean_array_get_size(v_keys_2824_);
v___x_2836_ = lean_nat_dec_lt(v_i_2826_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
lean_dec(v_i_2826_);
v___x_2837_ = lean_box(0);
return v___x_2837_;
}
else
{
lean_object* v_expr_2838_; uint64_t v_configKey_2839_; lean_object* v_k_x27_2840_; lean_object* v_expr_2841_; uint64_t v_configKey_2842_; uint8_t v___x_2843_; 
v_expr_2838_ = lean_ctor_get(v_k_2827_, 0);
v_configKey_2839_ = lean_ctor_get_uint64(v_k_2827_, sizeof(void*)*1);
v_k_x27_2840_ = lean_array_fget_borrowed(v_keys_2824_, v_i_2826_);
v_expr_2841_ = lean_ctor_get(v_k_x27_2840_, 0);
v_configKey_2842_ = lean_ctor_get_uint64(v_k_x27_2840_, sizeof(void*)*1);
v___x_2843_ = lean_expr_equal(v_expr_2838_, v_expr_2841_);
if (v___x_2843_ == 0)
{
v___y_2829_ = v___x_2843_;
goto v___jp_2828_;
}
else
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_uint64_dec_eq(v_configKey_2839_, v_configKey_2842_);
v___y_2829_ = v___x_2844_;
goto v___jp_2828_;
}
}
v___jp_2828_:
{
if (v___y_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_unsigned_to_nat(1u);
v___x_2831_ = lean_nat_add(v_i_2826_, v___x_2830_);
lean_dec(v_i_2826_);
v_i_2826_ = v___x_2831_;
goto _start;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_array_fget_borrowed(v_vals_2825_, v_i_2826_);
lean_dec(v_i_2826_);
lean_inc(v___x_2833_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2845_, lean_object* v_vals_2846_, lean_object* v_i_2847_, lean_object* v_k_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_2845_, v_vals_2846_, v_i_2847_, v_k_2848_);
lean_dec_ref(v_k_2848_);
lean_dec_ref(v_vals_2846_);
lean_dec_ref(v_keys_2845_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object* v_x_2850_, size_t v_x_2851_, lean_object* v_x_2852_){
_start:
{
if (lean_obj_tag(v_x_2850_) == 0)
{
lean_object* v_es_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2881_; 
v_es_2853_ = lean_ctor_get(v_x_2850_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2850_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2855_ = v_x_2850_;
v_isShared_2856_ = v_isSharedCheck_2881_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_es_2853_);
lean_dec(v_x_2850_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2881_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; size_t v___x_2860_; lean_object* v_j_2861_; lean_object* v___x_2862_; 
v___x_2857_ = lean_box(2);
v___x_2858_ = ((size_t)5ULL);
v___x_2859_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2860_ = lean_usize_land(v_x_2851_, v___x_2859_);
v_j_2861_ = lean_usize_to_nat(v___x_2860_);
v___x_2862_ = lean_array_get(v___x_2857_, v_es_2853_, v_j_2861_);
lean_dec(v_j_2861_);
lean_dec_ref(v_es_2853_);
switch(lean_obj_tag(v___x_2862_))
{
case 0:
{
lean_object* v_key_2863_; lean_object* v_val_2864_; uint8_t v___y_2866_; lean_object* v_expr_2871_; uint64_t v_configKey_2872_; lean_object* v_expr_2873_; uint64_t v_configKey_2874_; uint8_t v___x_2875_; 
v_key_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_key_2863_);
v_val_2864_ = lean_ctor_get(v___x_2862_, 1);
lean_inc(v_val_2864_);
lean_dec_ref(v___x_2862_);
v_expr_2871_ = lean_ctor_get(v_x_2852_, 0);
v_configKey_2872_ = lean_ctor_get_uint64(v_x_2852_, sizeof(void*)*1);
v_expr_2873_ = lean_ctor_get(v_key_2863_, 0);
lean_inc_ref(v_expr_2873_);
v_configKey_2874_ = lean_ctor_get_uint64(v_key_2863_, sizeof(void*)*1);
lean_dec(v_key_2863_);
v___x_2875_ = lean_expr_equal(v_expr_2871_, v_expr_2873_);
lean_dec_ref(v_expr_2873_);
if (v___x_2875_ == 0)
{
v___y_2866_ = v___x_2875_;
goto v___jp_2865_;
}
else
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_uint64_dec_eq(v_configKey_2872_, v_configKey_2874_);
v___y_2866_ = v___x_2876_;
goto v___jp_2865_;
}
v___jp_2865_:
{
if (v___y_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec(v_val_2864_);
lean_del_object(v___x_2855_);
v___x_2867_ = lean_box(0);
return v___x_2867_;
}
else
{
lean_object* v___x_2869_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 1);
lean_ctor_set(v___x_2855_, 0, v_val_2864_);
v___x_2869_ = v___x_2855_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_val_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
case 1:
{
lean_object* v_node_2877_; size_t v___x_2878_; 
lean_del_object(v___x_2855_);
v_node_2877_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_node_2877_);
lean_dec_ref(v___x_2862_);
v___x_2878_ = lean_usize_shift_right(v_x_2851_, v___x_2858_);
v_x_2850_ = v_node_2877_;
v_x_2851_ = v___x_2878_;
goto _start;
}
default: 
{
lean_object* v___x_2880_; 
lean_del_object(v___x_2855_);
v___x_2880_ = lean_box(0);
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_ks_2882_; lean_object* v_vs_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_ks_2882_ = lean_ctor_get(v_x_2850_, 0);
lean_inc_ref(v_ks_2882_);
v_vs_2883_ = lean_ctor_get(v_x_2850_, 1);
lean_inc_ref(v_vs_2883_);
lean_dec_ref(v_x_2850_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v___x_2885_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_ks_2882_, v_vs_2883_, v___x_2884_, v_x_2852_);
lean_dec_ref(v_vs_2883_);
lean_dec_ref(v_ks_2882_);
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object* v_x_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_){
_start:
{
size_t v_x_2320__boxed_2889_; lean_object* v_res_2890_; 
v_x_2320__boxed_2889_ = lean_unbox_usize(v_x_2887_);
lean_dec(v_x_2887_);
v_res_2890_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2886_, v_x_2320__boxed_2889_, v_x_2888_);
lean_dec_ref(v_x_2888_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object* v_x_2891_, lean_object* v_x_2892_){
_start:
{
lean_object* v_expr_2893_; uint64_t v_configKey_2894_; uint64_t v___x_2895_; uint64_t v___x_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
v_expr_2893_ = lean_ctor_get(v_x_2892_, 0);
v_configKey_2894_ = lean_ctor_get_uint64(v_x_2892_, sizeof(void*)*1);
v___x_2895_ = l_Lean_Expr_hash(v_expr_2893_);
v___x_2896_ = lean_uint64_mix_hash(v___x_2895_, v_configKey_2894_);
v___x_2897_ = lean_uint64_to_usize(v___x_2896_);
v___x_2898_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2891_, v___x_2897_, v_x_2892_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_2899_, v_x_2900_);
lean_dec_ref(v_x_2900_);
return v_res_2901_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_2904_ = l_Lean_stringToMessageData(v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
switch(lean_obj_tag(v_e_2905_))
{
case 0:
{
lean_object* v_deBruijnIndex_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_deBruijnIndex_2911_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_deBruijnIndex_2911_);
lean_dec_ref(v_e_2905_);
v___x_2912_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_2913_ = l_Lean_mkBVar(v_deBruijnIndex_2911_);
v___x_2914_ = l_Lean_MessageData_ofExpr(v___x_2913_);
v___x_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2912_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2915_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2916_;
}
case 1:
{
lean_object* v_fvarId_2917_; lean_object* v___x_2918_; 
v_fvarId_2917_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_fvarId_2917_);
lean_dec_ref(v_e_2905_);
v___x_2918_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2917_, v_a_2906_, v_a_2908_, v_a_2909_);
return v___x_2918_;
}
case 2:
{
lean_object* v_mvarId_2919_; lean_object* v___x_2920_; 
v_mvarId_2919_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_mvarId_2919_);
lean_dec_ref(v_e_2905_);
v___x_2920_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2919_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2920_;
}
case 3:
{
lean_object* v_u_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_u_2921_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_u_2921_);
lean_dec_ref(v_e_2905_);
v___x_2922_ = l_Lean_Level_succ___override(v_u_2921_);
v___x_2923_ = l_Lean_mkSort(v___x_2922_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
case 4:
{
lean_object* v_us_2925_; 
v_us_2925_ = lean_ctor_get(v_e_2905_, 1);
lean_inc(v_us_2925_);
if (lean_obj_tag(v_us_2925_) == 0)
{
lean_object* v_declName_2926_; lean_object* v___x_2927_; 
v_declName_2926_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_declName_2926_);
lean_dec_ref(v_e_2905_);
v___x_2927_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2926_, v_us_2925_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2927_;
}
else
{
uint8_t v_cacheInferType_2928_; 
v_cacheInferType_2928_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2928_ == 0)
{
lean_object* v_declName_2929_; lean_object* v___x_2930_; 
v_declName_2929_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_declName_2929_);
lean_dec_ref(v_e_2905_);
v___x_2930_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2929_, v_us_2925_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2930_;
}
else
{
lean_object* v_declName_2931_; uint8_t v___x_2932_; 
v_declName_2931_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_declName_2931_);
v___x_2932_ = l_Lean_Expr_hasMVar(v_e_2905_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2985_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2985_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2985_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v_cache_2939_; lean_object* v_inferType_2940_; lean_object* v___x_2941_; 
v___x_2938_ = lean_st_ref_get(v_a_2907_);
v_cache_2939_ = lean_ctor_get(v___x_2938_, 1);
lean_inc_ref(v_cache_2939_);
lean_dec(v___x_2938_);
v_inferType_2940_ = lean_ctor_get(v_cache_2939_, 0);
lean_inc_ref(v_inferType_2940_);
lean_dec_ref(v_cache_2939_);
v___x_2941_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_2940_, v_a_2934_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; 
lean_del_object(v___x_2936_);
v___x_2942_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2931_, v_us_2925_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; uint8_t v___x_2944_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
v___x_2944_ = l_Lean_Expr_hasMVar(v_a_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2979_; 
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v___x_2942_, 0);
lean_dec(v_unused_2980_);
v___x_2946_ = v___x_2942_;
v_isShared_2947_ = v_isSharedCheck_2979_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v___x_2942_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2979_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v_cache_2949_; lean_object* v_mctx_2950_; lean_object* v_zetaDeltaFVarIds_2951_; lean_object* v_postponed_2952_; lean_object* v_diag_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2978_; 
v___x_2948_ = lean_st_ref_take(v_a_2907_);
v_cache_2949_ = lean_ctor_get(v___x_2948_, 1);
v_mctx_2950_ = lean_ctor_get(v___x_2948_, 0);
v_zetaDeltaFVarIds_2951_ = lean_ctor_get(v___x_2948_, 2);
v_postponed_2952_ = lean_ctor_get(v___x_2948_, 3);
v_diag_2953_ = lean_ctor_get(v___x_2948_, 4);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2955_ = v___x_2948_;
v_isShared_2956_ = v_isSharedCheck_2978_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_diag_2953_);
lean_inc(v_postponed_2952_);
lean_inc(v_zetaDeltaFVarIds_2951_);
lean_inc(v_cache_2949_);
lean_inc(v_mctx_2950_);
lean_dec(v___x_2948_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2978_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_inferType_2957_; lean_object* v_funInfo_2958_; lean_object* v_synthInstance_2959_; lean_object* v_whnf_2960_; lean_object* v_defEqTrans_2961_; lean_object* v_defEqPerm_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2977_; 
v_inferType_2957_ = lean_ctor_get(v_cache_2949_, 0);
v_funInfo_2958_ = lean_ctor_get(v_cache_2949_, 1);
v_synthInstance_2959_ = lean_ctor_get(v_cache_2949_, 2);
v_whnf_2960_ = lean_ctor_get(v_cache_2949_, 3);
v_defEqTrans_2961_ = lean_ctor_get(v_cache_2949_, 4);
v_defEqPerm_2962_ = lean_ctor_get(v_cache_2949_, 5);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_cache_2949_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2964_ = v_cache_2949_;
v_isShared_2965_ = v_isSharedCheck_2977_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_defEqPerm_2962_);
lean_inc(v_defEqTrans_2961_);
lean_inc(v_whnf_2960_);
lean_inc(v_synthInstance_2959_);
lean_inc(v_funInfo_2958_);
lean_inc(v_inferType_2957_);
lean_dec(v_cache_2949_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2977_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
lean_inc(v_a_2943_);
v___x_2966_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_2957_, v_a_2934_, v_a_2943_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2966_);
v___x_2968_ = v___x_2964_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_funInfo_2958_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_synthInstance_2959_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_whnf_2960_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_defEqTrans_2961_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v_defEqPerm_2962_);
v___x_2968_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2968_);
v___x_2970_ = v___x_2955_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_mctx_2950_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_zetaDeltaFVarIds_2951_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_postponed_2952_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_diag_2953_);
v___x_2970_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = lean_st_ref_set(v_a_2907_, v___x_2970_);
if (v_isShared_2947_ == 0)
{
v___x_2973_ = v___x_2946_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2943_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2943_);
lean_dec(v_a_2934_);
return v___x_2942_;
}
}
else
{
lean_dec(v_a_2934_);
return v___x_2942_;
}
}
else
{
lean_object* v_val_2981_; lean_object* v___x_2983_; 
lean_dec(v_a_2934_);
lean_dec(v_declName_2931_);
lean_dec(v_us_2925_);
v_val_2981_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_val_2981_);
lean_dec_ref(v___x_2941_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v_val_2981_);
v___x_2983_ = v___x_2936_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_val_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_declName_2931_);
lean_dec(v_us_2925_);
v_a_2986_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2933_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2933_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v___x_2994_; 
lean_dec_ref(v_e_2905_);
v___x_2994_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2931_, v_us_2925_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_2994_;
}
}
}
}
case 5:
{
lean_object* v_fn_2995_; uint8_t v_cacheInferType_2996_; lean_object* v_nargs_2997_; lean_object* v___x_2998_; lean_object* v_dummy_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_fn_2995_ = lean_ctor_get(v_e_2905_, 0);
v_cacheInferType_2996_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*7 + 3);
v_nargs_2997_ = l_Lean_Expr_getAppNumArgs(v_e_2905_);
v___x_2998_ = l_Lean_Expr_getAppFn(v_fn_2995_);
v_dummy_2999_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_2997_);
v___x_3000_ = lean_mk_array(v_nargs_2997_, v_dummy_2999_);
v___x_3001_ = lean_unsigned_to_nat(1u);
v___x_3002_ = lean_nat_sub(v_nargs_2997_, v___x_3001_);
lean_dec(v_nargs_2997_);
lean_inc_ref(v_e_2905_);
v___x_3003_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2905_, v___x_3000_, v___x_3002_);
if (v_cacheInferType_2996_ == 0)
{
lean_object* v___x_3004_; 
lean_dec_ref(v_e_2905_);
v___x_3004_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_2998_, v___x_3003_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec_ref(v___x_3003_);
return v___x_3004_;
}
else
{
uint8_t v___x_3005_; 
v___x_3005_ = l_Lean_Expr_hasMVar(v_e_2905_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2905_, v_a_2906_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3058_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3058_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3058_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v_cache_3012_; lean_object* v_inferType_3013_; lean_object* v___x_3014_; 
v___x_3011_ = lean_st_ref_get(v_a_2907_);
v_cache_3012_ = lean_ctor_get(v___x_3011_, 1);
lean_inc_ref(v_cache_3012_);
lean_dec(v___x_3011_);
v_inferType_3013_ = lean_ctor_get(v_cache_3012_, 0);
lean_inc_ref(v_inferType_3013_);
lean_dec_ref(v_cache_3012_);
v___x_3014_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3013_, v_a_3007_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3015_; 
lean_del_object(v___x_3009_);
v___x_3015_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_2998_, v___x_3003_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec_ref(v___x_3003_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; uint8_t v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
v___x_3017_ = l_Lean_Expr_hasMVar(v_a_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3052_; 
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___x_3015_, 0);
lean_dec(v_unused_3053_);
v___x_3019_ = v___x_3015_;
v_isShared_3020_ = v_isSharedCheck_3052_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v___x_3015_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3052_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v_cache_3022_; lean_object* v_mctx_3023_; lean_object* v_zetaDeltaFVarIds_3024_; lean_object* v_postponed_3025_; lean_object* v_diag_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3051_; 
v___x_3021_ = lean_st_ref_take(v_a_2907_);
v_cache_3022_ = lean_ctor_get(v___x_3021_, 1);
v_mctx_3023_ = lean_ctor_get(v___x_3021_, 0);
v_zetaDeltaFVarIds_3024_ = lean_ctor_get(v___x_3021_, 2);
v_postponed_3025_ = lean_ctor_get(v___x_3021_, 3);
v_diag_3026_ = lean_ctor_get(v___x_3021_, 4);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3028_ = v___x_3021_;
v_isShared_3029_ = v_isSharedCheck_3051_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_diag_3026_);
lean_inc(v_postponed_3025_);
lean_inc(v_zetaDeltaFVarIds_3024_);
lean_inc(v_cache_3022_);
lean_inc(v_mctx_3023_);
lean_dec(v___x_3021_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3051_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v_inferType_3030_; lean_object* v_funInfo_3031_; lean_object* v_synthInstance_3032_; lean_object* v_whnf_3033_; lean_object* v_defEqTrans_3034_; lean_object* v_defEqPerm_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3050_; 
v_inferType_3030_ = lean_ctor_get(v_cache_3022_, 0);
v_funInfo_3031_ = lean_ctor_get(v_cache_3022_, 1);
v_synthInstance_3032_ = lean_ctor_get(v_cache_3022_, 2);
v_whnf_3033_ = lean_ctor_get(v_cache_3022_, 3);
v_defEqTrans_3034_ = lean_ctor_get(v_cache_3022_, 4);
v_defEqPerm_3035_ = lean_ctor_get(v_cache_3022_, 5);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_cache_3022_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3037_ = v_cache_3022_;
v_isShared_3038_ = v_isSharedCheck_3050_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_defEqPerm_3035_);
lean_inc(v_defEqTrans_3034_);
lean_inc(v_whnf_3033_);
lean_inc(v_synthInstance_3032_);
lean_inc(v_funInfo_3031_);
lean_inc(v_inferType_3030_);
lean_dec(v_cache_3022_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3050_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_inc(v_a_3016_);
v___x_3039_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3030_, v_a_3007_, v_a_3016_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3039_);
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_funInfo_3031_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_synthInstance_3032_);
lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_whnf_3033_);
lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_defEqTrans_3034_);
lean_ctor_set(v_reuseFailAlloc_3049_, 5, v_defEqPerm_3035_);
v___x_3041_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3041_);
v___x_3043_ = v___x_3028_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_mctx_3023_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_zetaDeltaFVarIds_3024_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_postponed_3025_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_diag_3026_);
v___x_3043_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3044_ = lean_st_ref_set(v_a_2907_, v___x_3043_);
if (v_isShared_3020_ == 0)
{
v___x_3046_ = v___x_3019_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3016_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3016_);
lean_dec(v_a_3007_);
return v___x_3015_;
}
}
else
{
lean_dec(v_a_3007_);
return v___x_3015_;
}
}
else
{
lean_object* v_val_3054_; lean_object* v___x_3056_; 
lean_dec(v_a_3007_);
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_2998_);
v_val_3054_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_val_3054_);
lean_dec_ref(v___x_3014_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v_val_3054_);
v___x_3056_ = v___x_3009_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_val_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_2998_);
v_a_3059_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3006_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3006_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v___x_3067_; 
lean_dec_ref(v_e_2905_);
v___x_3067_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_2998_, v___x_3003_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec_ref(v___x_3003_);
return v___x_3067_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3068_; 
v_cacheInferType_3068_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3068_ == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3069_;
}
else
{
uint8_t v___x_3070_; 
v___x_3070_ = l_Lean_Expr_hasMVar(v_e_2905_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
lean_inc_ref(v_e_2905_);
v___x_3071_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2905_, v_a_2906_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3123_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3123_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3123_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v_cache_3077_; lean_object* v_inferType_3078_; lean_object* v___x_3079_; 
v___x_3076_ = lean_st_ref_get(v_a_2907_);
v_cache_3077_ = lean_ctor_get(v___x_3076_, 1);
lean_inc_ref(v_cache_3077_);
lean_dec(v___x_3076_);
v_inferType_3078_ = lean_ctor_get(v_cache_3077_, 0);
lean_inc_ref(v_inferType_3078_);
lean_dec_ref(v_cache_3077_);
v___x_3079_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3078_, v_a_3072_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3080_; 
lean_del_object(v___x_3074_);
v___x_3080_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; uint8_t v___x_3082_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
v___x_3082_ = l_Lean_Expr_hasMVar(v_a_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3118_);
v___x_3084_ = v___x_3080_;
v_isShared_3085_ = v_isSharedCheck_3117_;
goto v_resetjp_3083_;
}
else
{
lean_dec(v___x_3080_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3117_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v_cache_3087_; lean_object* v_mctx_3088_; lean_object* v_zetaDeltaFVarIds_3089_; lean_object* v_postponed_3090_; lean_object* v_diag_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3116_; 
v___x_3086_ = lean_st_ref_take(v_a_2907_);
v_cache_3087_ = lean_ctor_get(v___x_3086_, 1);
v_mctx_3088_ = lean_ctor_get(v___x_3086_, 0);
v_zetaDeltaFVarIds_3089_ = lean_ctor_get(v___x_3086_, 2);
v_postponed_3090_ = lean_ctor_get(v___x_3086_, 3);
v_diag_3091_ = lean_ctor_get(v___x_3086_, 4);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3093_ = v___x_3086_;
v_isShared_3094_ = v_isSharedCheck_3116_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_diag_3091_);
lean_inc(v_postponed_3090_);
lean_inc(v_zetaDeltaFVarIds_3089_);
lean_inc(v_cache_3087_);
lean_inc(v_mctx_3088_);
lean_dec(v___x_3086_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3116_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_inferType_3095_; lean_object* v_funInfo_3096_; lean_object* v_synthInstance_3097_; lean_object* v_whnf_3098_; lean_object* v_defEqTrans_3099_; lean_object* v_defEqPerm_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3115_; 
v_inferType_3095_ = lean_ctor_get(v_cache_3087_, 0);
v_funInfo_3096_ = lean_ctor_get(v_cache_3087_, 1);
v_synthInstance_3097_ = lean_ctor_get(v_cache_3087_, 2);
v_whnf_3098_ = lean_ctor_get(v_cache_3087_, 3);
v_defEqTrans_3099_ = lean_ctor_get(v_cache_3087_, 4);
v_defEqPerm_3100_ = lean_ctor_get(v_cache_3087_, 5);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_cache_3087_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3102_ = v_cache_3087_;
v_isShared_3103_ = v_isSharedCheck_3115_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_defEqPerm_3100_);
lean_inc(v_defEqTrans_3099_);
lean_inc(v_whnf_3098_);
lean_inc(v_synthInstance_3097_);
lean_inc(v_funInfo_3096_);
lean_inc(v_inferType_3095_);
lean_dec(v_cache_3087_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3115_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
lean_inc(v_a_3081_);
v___x_3104_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3095_, v_a_3072_, v_a_3081_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3104_);
v___x_3106_ = v___x_3102_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_funInfo_3096_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_synthInstance_3097_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_whnf_3098_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_defEqTrans_3099_);
lean_ctor_set(v_reuseFailAlloc_3114_, 5, v_defEqPerm_3100_);
v___x_3106_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3108_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 1, v___x_3106_);
v___x_3108_ = v___x_3093_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_mctx_3088_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_zetaDeltaFVarIds_3089_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_postponed_3090_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_diag_3091_);
v___x_3108_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_st_ref_set(v_a_2907_, v___x_3108_);
if (v_isShared_3085_ == 0)
{
v___x_3111_ = v___x_3084_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3081_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3081_);
lean_dec(v_a_3072_);
return v___x_3080_;
}
}
else
{
lean_dec(v_a_3072_);
return v___x_3080_;
}
}
else
{
lean_object* v_val_3119_; lean_object* v___x_3121_; 
lean_dec(v_a_3072_);
lean_dec_ref(v_e_2905_);
v_val_3119_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_val_3119_);
lean_dec_ref(v___x_3079_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v_val_3119_);
v___x_3121_ = v___x_3074_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_val_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v_e_2905_);
v_a_3124_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3071_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3071_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v___x_3132_; 
v___x_3132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3132_;
}
}
}
case 9:
{
lean_object* v_a_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v_a_3133_ = lean_ctor_get(v_e_2905_, 0);
lean_inc_ref(v_a_3133_);
lean_dec_ref(v_e_2905_);
v___x_3134_ = l_Lean_Literal_type(v_a_3133_);
lean_dec_ref(v_a_3133_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
case 10:
{
lean_object* v_expr_3136_; 
v_expr_3136_ = lean_ctor_get(v_e_2905_, 1);
lean_inc_ref(v_expr_3136_);
lean_dec_ref(v_e_2905_);
v_e_2905_ = v_expr_3136_;
goto _start;
}
case 11:
{
uint8_t v_cacheInferType_3138_; 
v_cacheInferType_3138_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3138_ == 0)
{
lean_object* v_typeName_3139_; lean_object* v_idx_3140_; lean_object* v_struct_3141_; lean_object* v___x_3142_; 
v_typeName_3139_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_typeName_3139_);
v_idx_3140_ = lean_ctor_get(v_e_2905_, 1);
lean_inc(v_idx_3140_);
v_struct_3141_ = lean_ctor_get(v_e_2905_, 2);
lean_inc_ref(v_struct_3141_);
lean_dec_ref(v_e_2905_);
v___x_3142_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3139_, v_idx_3140_, v_struct_3141_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3142_;
}
else
{
lean_object* v_typeName_3143_; lean_object* v_idx_3144_; lean_object* v_struct_3145_; uint8_t v___x_3146_; 
v_typeName_3143_ = lean_ctor_get(v_e_2905_, 0);
lean_inc(v_typeName_3143_);
v_idx_3144_ = lean_ctor_get(v_e_2905_, 1);
lean_inc(v_idx_3144_);
v_struct_3145_ = lean_ctor_get(v_e_2905_, 2);
lean_inc_ref(v_struct_3145_);
v___x_3146_ = l_Lean_Expr_hasMVar(v_e_2905_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2905_, v_a_2906_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3199_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3199_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3199_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v_cache_3153_; lean_object* v_inferType_3154_; lean_object* v___x_3155_; 
v___x_3152_ = lean_st_ref_get(v_a_2907_);
v_cache_3153_ = lean_ctor_get(v___x_3152_, 1);
lean_inc_ref(v_cache_3153_);
lean_dec(v___x_3152_);
v_inferType_3154_ = lean_ctor_get(v_cache_3153_, 0);
lean_inc_ref(v_inferType_3154_);
lean_dec_ref(v_cache_3153_);
v___x_3155_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3154_, v_a_3148_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v___x_3156_; 
lean_del_object(v___x_3150_);
v___x_3156_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3143_, v_idx_3144_, v_struct_3145_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; uint8_t v___x_3158_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
v___x_3158_ = l_Lean_Expr_hasMVar(v_a_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3193_; 
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v___x_3156_, 0);
lean_dec(v_unused_3194_);
v___x_3160_ = v___x_3156_;
v_isShared_3161_ = v_isSharedCheck_3193_;
goto v_resetjp_3159_;
}
else
{
lean_dec(v___x_3156_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3193_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v_cache_3163_; lean_object* v_mctx_3164_; lean_object* v_zetaDeltaFVarIds_3165_; lean_object* v_postponed_3166_; lean_object* v_diag_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3192_; 
v___x_3162_ = lean_st_ref_take(v_a_2907_);
v_cache_3163_ = lean_ctor_get(v___x_3162_, 1);
v_mctx_3164_ = lean_ctor_get(v___x_3162_, 0);
v_zetaDeltaFVarIds_3165_ = lean_ctor_get(v___x_3162_, 2);
v_postponed_3166_ = lean_ctor_get(v___x_3162_, 3);
v_diag_3167_ = lean_ctor_get(v___x_3162_, 4);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3169_ = v___x_3162_;
v_isShared_3170_ = v_isSharedCheck_3192_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_diag_3167_);
lean_inc(v_postponed_3166_);
lean_inc(v_zetaDeltaFVarIds_3165_);
lean_inc(v_cache_3163_);
lean_inc(v_mctx_3164_);
lean_dec(v___x_3162_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3192_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_inferType_3171_; lean_object* v_funInfo_3172_; lean_object* v_synthInstance_3173_; lean_object* v_whnf_3174_; lean_object* v_defEqTrans_3175_; lean_object* v_defEqPerm_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3191_; 
v_inferType_3171_ = lean_ctor_get(v_cache_3163_, 0);
v_funInfo_3172_ = lean_ctor_get(v_cache_3163_, 1);
v_synthInstance_3173_ = lean_ctor_get(v_cache_3163_, 2);
v_whnf_3174_ = lean_ctor_get(v_cache_3163_, 3);
v_defEqTrans_3175_ = lean_ctor_get(v_cache_3163_, 4);
v_defEqPerm_3176_ = lean_ctor_get(v_cache_3163_, 5);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_cache_3163_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3178_ = v_cache_3163_;
v_isShared_3179_ = v_isSharedCheck_3191_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_defEqPerm_3176_);
lean_inc(v_defEqTrans_3175_);
lean_inc(v_whnf_3174_);
lean_inc(v_synthInstance_3173_);
lean_inc(v_funInfo_3172_);
lean_inc(v_inferType_3171_);
lean_dec(v_cache_3163_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3191_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
lean_inc(v_a_3157_);
v___x_3180_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3171_, v_a_3148_, v_a_3157_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3180_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_funInfo_3172_);
lean_ctor_set(v_reuseFailAlloc_3190_, 2, v_synthInstance_3173_);
lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_whnf_3174_);
lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_defEqTrans_3175_);
lean_ctor_set(v_reuseFailAlloc_3190_, 5, v_defEqPerm_3176_);
v___x_3182_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3184_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 1, v___x_3182_);
v___x_3184_ = v___x_3169_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_mctx_3164_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_zetaDeltaFVarIds_3165_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_postponed_3166_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_diag_3167_);
v___x_3184_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = lean_st_ref_set(v_a_2907_, v___x_3184_);
if (v_isShared_3161_ == 0)
{
v___x_3187_ = v___x_3160_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3157_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3157_);
lean_dec(v_a_3148_);
return v___x_3156_;
}
}
else
{
lean_dec(v_a_3148_);
return v___x_3156_;
}
}
else
{
lean_object* v_val_3195_; lean_object* v___x_3197_; 
lean_dec(v_a_3148_);
lean_dec_ref(v_struct_3145_);
lean_dec(v_idx_3144_);
lean_dec(v_typeName_3143_);
v_val_3195_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_val_3195_);
lean_dec_ref(v___x_3155_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v_val_3195_);
v___x_3197_ = v___x_3150_;
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
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_struct_3145_);
lean_dec(v_idx_3144_);
lean_dec(v_typeName_3143_);
v_a_3200_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3147_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3147_);
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
lean_object* v___x_3208_; 
lean_dec_ref(v_e_2905_);
v___x_3208_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3143_, v_idx_3144_, v_struct_3145_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3208_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3209_; 
v_cacheInferType_3209_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3209_ == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3210_;
}
else
{
uint8_t v___x_3211_; 
v___x_3211_ = l_Lean_Expr_hasMVar(v_e_2905_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_inc_ref(v_e_2905_);
v___x_3212_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2905_, v_a_2906_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3264_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3264_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3264_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v_cache_3218_; lean_object* v_inferType_3219_; lean_object* v___x_3220_; 
v___x_3217_ = lean_st_ref_get(v_a_2907_);
v_cache_3218_ = lean_ctor_get(v___x_3217_, 1);
lean_inc_ref(v_cache_3218_);
lean_dec(v___x_3217_);
v_inferType_3219_ = lean_ctor_get(v_cache_3218_, 0);
lean_inc_ref(v_inferType_3219_);
lean_dec_ref(v_cache_3218_);
v___x_3220_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3219_, v_a_3213_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3221_; 
lean_del_object(v___x_3215_);
v___x_3221_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; uint8_t v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
v___x_3223_ = l_Lean_Expr_hasMVar(v_a_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3258_; 
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v___x_3221_, 0);
lean_dec(v_unused_3259_);
v___x_3225_ = v___x_3221_;
v_isShared_3226_ = v_isSharedCheck_3258_;
goto v_resetjp_3224_;
}
else
{
lean_dec(v___x_3221_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3258_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v_cache_3228_; lean_object* v_mctx_3229_; lean_object* v_zetaDeltaFVarIds_3230_; lean_object* v_postponed_3231_; lean_object* v_diag_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3257_; 
v___x_3227_ = lean_st_ref_take(v_a_2907_);
v_cache_3228_ = lean_ctor_get(v___x_3227_, 1);
v_mctx_3229_ = lean_ctor_get(v___x_3227_, 0);
v_zetaDeltaFVarIds_3230_ = lean_ctor_get(v___x_3227_, 2);
v_postponed_3231_ = lean_ctor_get(v___x_3227_, 3);
v_diag_3232_ = lean_ctor_get(v___x_3227_, 4);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3234_ = v___x_3227_;
v_isShared_3235_ = v_isSharedCheck_3257_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_diag_3232_);
lean_inc(v_postponed_3231_);
lean_inc(v_zetaDeltaFVarIds_3230_);
lean_inc(v_cache_3228_);
lean_inc(v_mctx_3229_);
lean_dec(v___x_3227_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3257_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_inferType_3236_; lean_object* v_funInfo_3237_; lean_object* v_synthInstance_3238_; lean_object* v_whnf_3239_; lean_object* v_defEqTrans_3240_; lean_object* v_defEqPerm_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3256_; 
v_inferType_3236_ = lean_ctor_get(v_cache_3228_, 0);
v_funInfo_3237_ = lean_ctor_get(v_cache_3228_, 1);
v_synthInstance_3238_ = lean_ctor_get(v_cache_3228_, 2);
v_whnf_3239_ = lean_ctor_get(v_cache_3228_, 3);
v_defEqTrans_3240_ = lean_ctor_get(v_cache_3228_, 4);
v_defEqPerm_3241_ = lean_ctor_get(v_cache_3228_, 5);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_cache_3228_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3243_ = v_cache_3228_;
v_isShared_3244_ = v_isSharedCheck_3256_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_defEqPerm_3241_);
lean_inc(v_defEqTrans_3240_);
lean_inc(v_whnf_3239_);
lean_inc(v_synthInstance_3238_);
lean_inc(v_funInfo_3237_);
lean_inc(v_inferType_3236_);
lean_dec(v_cache_3228_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3256_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_inc(v_a_3222_);
v___x_3245_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3236_, v_a_3213_, v_a_3222_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v___x_3245_);
v___x_3247_ = v___x_3243_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_funInfo_3237_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v_synthInstance_3238_);
lean_ctor_set(v_reuseFailAlloc_3255_, 3, v_whnf_3239_);
lean_ctor_set(v_reuseFailAlloc_3255_, 4, v_defEqTrans_3240_);
lean_ctor_set(v_reuseFailAlloc_3255_, 5, v_defEqPerm_3241_);
v___x_3247_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3249_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 1, v___x_3247_);
v___x_3249_ = v___x_3234_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_mctx_3229_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v_zetaDeltaFVarIds_3230_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v_postponed_3231_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v_diag_3232_);
v___x_3249_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = lean_st_ref_set(v_a_2907_, v___x_3249_);
if (v_isShared_3226_ == 0)
{
v___x_3252_ = v___x_3225_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3222_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3222_);
lean_dec(v_a_3213_);
return v___x_3221_;
}
}
else
{
lean_dec(v_a_3213_);
return v___x_3221_;
}
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; 
lean_dec(v_a_3213_);
lean_dec_ref(v_e_2905_);
v_val_3260_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_val_3260_);
lean_dec_ref(v___x_3220_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v_val_3260_);
v___x_3262_ = v___x_3215_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_val_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_e_2905_);
v_a_3265_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3212_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3212_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v___x_3273_; 
v___x_3273_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
return v___x_3273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b2_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_3282_, v_x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b2_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b2_3285_, v_x_3286_, v_x_3287_);
lean_dec_ref(v_x_3287_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3290_, v_x_3291_, v_x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object* v_00_u03b2_3294_, lean_object* v_x_3295_, size_t v_x_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3295_, v_x_3296_, v_x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
size_t v_x_3132__boxed_3303_; lean_object* v_res_3304_; 
v_x_3132__boxed_3303_ = lean_unbox_usize(v_x_3301_);
lean_dec(v_x_3301_);
v_res_3304_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(v_00_u03b2_3299_, v_x_3300_, v_x_3132__boxed_3303_, v_x_3302_);
lean_dec_ref(v_x_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object* v_00_u03b2_3305_, lean_object* v_x_3306_, size_t v_x_3307_, size_t v_x_3308_, lean_object* v_x_3309_, lean_object* v_x_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3306_, v_x_3307_, v_x_3308_, v_x_3309_, v_x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_){
_start:
{
size_t v_x_3143__boxed_3318_; size_t v_x_3144__boxed_3319_; lean_object* v_res_3320_; 
v_x_3143__boxed_3318_ = lean_unbox_usize(v_x_3314_);
lean_dec(v_x_3314_);
v_x_3144__boxed_3319_ = lean_unbox_usize(v_x_3315_);
lean_dec(v_x_3315_);
v_res_3320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(v_00_u03b2_3312_, v_x_3313_, v_x_3143__boxed_3318_, v_x_3144__boxed_3319_, v_x_3316_, v_x_3317_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3321_, lean_object* v_keys_3322_, lean_object* v_vals_3323_, lean_object* v_heq_3324_, lean_object* v_i_3325_, lean_object* v_k_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_3322_, v_vals_3323_, v_i_3325_, v_k_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_keys_3329_, lean_object* v_vals_3330_, lean_object* v_heq_3331_, lean_object* v_i_3332_, lean_object* v_k_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(v_00_u03b2_3328_, v_keys_3329_, v_vals_3330_, v_heq_3331_, v_i_3332_, v_k_3333_);
lean_dec_ref(v_k_3333_);
lean_dec_ref(v_vals_3330_);
lean_dec_ref(v_keys_3329_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3335_, lean_object* v_n_3336_, lean_object* v_k_3337_, lean_object* v_v_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v_n_3336_, v_k_3337_, v_v_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3340_, size_t v_depth_3341_, lean_object* v_keys_3342_, lean_object* v_vals_3343_, lean_object* v_heq_3344_, lean_object* v_i_3345_, lean_object* v_entries_3346_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_3341_, v_keys_3342_, v_vals_3343_, v_i_3345_, v_entries_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3348_, lean_object* v_depth_3349_, lean_object* v_keys_3350_, lean_object* v_vals_3351_, lean_object* v_heq_3352_, lean_object* v_i_3353_, lean_object* v_entries_3354_){
_start:
{
size_t v_depth_boxed_3355_; lean_object* v_res_3356_; 
v_depth_boxed_3355_ = lean_unbox_usize(v_depth_3349_);
lean_dec(v_depth_3349_);
v_res_3356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(v_00_u03b2_3348_, v_depth_boxed_3355_, v_keys_3350_, v_vals_3351_, v_heq_3352_, v_i_3353_, v_entries_3354_);
lean_dec_ref(v_vals_3351_);
lean_dec_ref(v_keys_3350_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_, lean_object* v_x_3360_, lean_object* v_x_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3358_, v_x_3359_, v_x_3360_, v_x_3361_);
return v___x_3362_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = l_Lean_maxRecDepthErrorMessage;
v___x_3369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3371_ = l_Lean_MessageData_ofFormat(v___x_3370_);
return v___x_3371_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3372_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3373_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3374_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___x_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_ref_3375_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3383_, lean_object* v_ref_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3384_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3391_, lean_object* v_ref_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3391_, v_ref_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; uint8_t v___y_3409_; uint8_t v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; uint8_t v___y_3415_; lean_object* v___y_3416_; uint8_t v___y_3417_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v_fileName_3518_; lean_object* v_fileMap_3519_; lean_object* v_options_3520_; lean_object* v_currRecDepth_3521_; lean_object* v_maxRecDepth_3522_; lean_object* v_ref_3523_; lean_object* v_currNamespace_3524_; lean_object* v_openDecls_3525_; lean_object* v_initHeartbeats_3526_; lean_object* v_maxHeartbeats_3527_; lean_object* v_quotContext_3528_; lean_object* v_currMacroScope_3529_; uint8_t v_diag_3530_; lean_object* v_cancelTk_x3f_3531_; uint8_t v_suppressElabErrors_3532_; lean_object* v_inheritedTraceOptions_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3551_; 
v_fileName_3518_ = lean_ctor_get(v_a_3402_, 0);
v_fileMap_3519_ = lean_ctor_get(v_a_3402_, 1);
v_options_3520_ = lean_ctor_get(v_a_3402_, 2);
v_currRecDepth_3521_ = lean_ctor_get(v_a_3402_, 3);
v_maxRecDepth_3522_ = lean_ctor_get(v_a_3402_, 4);
v_ref_3523_ = lean_ctor_get(v_a_3402_, 5);
v_currNamespace_3524_ = lean_ctor_get(v_a_3402_, 6);
v_openDecls_3525_ = lean_ctor_get(v_a_3402_, 7);
v_initHeartbeats_3526_ = lean_ctor_get(v_a_3402_, 8);
v_maxHeartbeats_3527_ = lean_ctor_get(v_a_3402_, 9);
v_quotContext_3528_ = lean_ctor_get(v_a_3402_, 10);
v_currMacroScope_3529_ = lean_ctor_get(v_a_3402_, 11);
v_diag_3530_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*14);
v_cancelTk_x3f_3531_ = lean_ctor_get(v_a_3402_, 12);
v_suppressElabErrors_3532_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3533_ = lean_ctor_get(v_a_3402_, 13);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_a_3402_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3535_ = v_a_3402_;
v_isShared_3536_ = v_isSharedCheck_3551_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_inheritedTraceOptions_3533_);
lean_inc(v_cancelTk_x3f_3531_);
lean_inc(v_currMacroScope_3529_);
lean_inc(v_quotContext_3528_);
lean_inc(v_maxHeartbeats_3527_);
lean_inc(v_initHeartbeats_3526_);
lean_inc(v_openDecls_3525_);
lean_inc(v_currNamespace_3524_);
lean_inc(v_ref_3523_);
lean_inc(v_maxRecDepth_3522_);
lean_inc(v_currRecDepth_3521_);
lean_inc(v_options_3520_);
lean_inc(v_fileMap_3519_);
lean_inc(v_fileName_3518_);
lean_dec(v_a_3402_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3551_;
goto v_resetjp_3534_;
}
v___jp_3405_:
{
lean_object* v___x_3418_; uint8_t v_foApprox_3419_; uint8_t v_ctxApprox_3420_; uint8_t v_quasiPatternApprox_3421_; uint8_t v_constApprox_3422_; uint8_t v_isDefEqStuckEx_3423_; uint8_t v_unificationHints_3424_; uint8_t v_proofIrrelevance_3425_; uint8_t v_assignSyntheticOpaque_3426_; uint8_t v_offsetCnstrs_3427_; uint8_t v_transparency_3428_; uint8_t v_univApprox_3429_; uint8_t v_zetaUnused_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3444_; 
v___x_3418_ = l_Lean_Meta_Context_config(v___y_3411_);
lean_dec_ref(v___y_3411_);
v_foApprox_3419_ = lean_ctor_get_uint8(v___x_3418_, 0);
v_ctxApprox_3420_ = lean_ctor_get_uint8(v___x_3418_, 1);
v_quasiPatternApprox_3421_ = lean_ctor_get_uint8(v___x_3418_, 2);
v_constApprox_3422_ = lean_ctor_get_uint8(v___x_3418_, 3);
v_isDefEqStuckEx_3423_ = lean_ctor_get_uint8(v___x_3418_, 4);
v_unificationHints_3424_ = lean_ctor_get_uint8(v___x_3418_, 5);
v_proofIrrelevance_3425_ = lean_ctor_get_uint8(v___x_3418_, 6);
v_assignSyntheticOpaque_3426_ = lean_ctor_get_uint8(v___x_3418_, 7);
v_offsetCnstrs_3427_ = lean_ctor_get_uint8(v___x_3418_, 8);
v_transparency_3428_ = lean_ctor_get_uint8(v___x_3418_, 9);
v_univApprox_3429_ = lean_ctor_get_uint8(v___x_3418_, 11);
v_zetaUnused_3430_ = lean_ctor_get_uint8(v___x_3418_, 17);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3432_ = v___x_3418_;
v_isShared_3433_ = v_isSharedCheck_3444_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v___x_3418_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3444_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
uint8_t v___x_3434_; uint8_t v___x_3435_; uint8_t v___x_3436_; lean_object* v___x_3438_; 
v___x_3434_ = 1;
v___x_3435_ = 0;
v___x_3436_ = 2;
if (v_isShared_3433_ == 0)
{
v___x_3438_ = v___x_3432_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 0, v_foApprox_3419_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 1, v_ctxApprox_3420_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 2, v_quasiPatternApprox_3421_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 3, v_constApprox_3422_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 4, v_isDefEqStuckEx_3423_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 5, v_unificationHints_3424_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 6, v_proofIrrelevance_3425_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 7, v_assignSyntheticOpaque_3426_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 8, v_offsetCnstrs_3427_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 9, v_transparency_3428_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 11, v_univApprox_3429_);
lean_ctor_set_uint8(v_reuseFailAlloc_3443_, 17, v_zetaUnused_3430_);
v___x_3438_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
uint64_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_ctor_set_uint8(v___x_3438_, 10, v___x_3435_);
lean_ctor_set_uint8(v___x_3438_, 12, v___x_3434_);
lean_ctor_set_uint8(v___x_3438_, 13, v___x_3434_);
lean_ctor_set_uint8(v___x_3438_, 14, v___x_3436_);
lean_ctor_set_uint8(v___x_3438_, 15, v___x_3434_);
lean_ctor_set_uint8(v___x_3438_, 16, v___x_3434_);
lean_ctor_set_uint8(v___x_3438_, 18, v___x_3434_);
v___x_3439_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3438_);
v___x_3440_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set_uint64(v___x_3440_, sizeof(void*)*1, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
lean_ctor_set(v___x_3441_, 1, v___y_3416_);
lean_ctor_set(v___x_3441_, 2, v___y_3414_);
lean_ctor_set(v___x_3441_, 3, v___y_3407_);
lean_ctor_set(v___x_3441_, 4, v___y_3412_);
lean_ctor_set(v___x_3441_, 5, v___y_3408_);
lean_ctor_set(v___x_3441_, 6, v___y_3413_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7, v___y_3417_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7 + 1, v___y_3410_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7 + 2, v___y_3409_);
lean_ctor_set_uint8(v___x_3441_, sizeof(void*)*7 + 3, v___y_3415_);
v___x_3442_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3399_, v___x_3441_, v_a_3401_, v___y_3406_, v_a_3403_);
lean_dec(v_a_3403_);
lean_dec_ref(v___y_3406_);
lean_dec(v_a_3401_);
lean_dec_ref(v___x_3441_);
return v___x_3442_;
}
}
}
v___jp_3445_:
{
lean_object* v___x_3448_; uint8_t v_foApprox_3449_; uint8_t v_ctxApprox_3450_; uint8_t v_quasiPatternApprox_3451_; uint8_t v_constApprox_3452_; uint8_t v_isDefEqStuckEx_3453_; uint8_t v_unificationHints_3454_; uint8_t v_proofIrrelevance_3455_; uint8_t v_assignSyntheticOpaque_3456_; uint8_t v_offsetCnstrs_3457_; uint8_t v_etaStruct_3458_; uint8_t v_univApprox_3459_; uint8_t v_iota_3460_; uint8_t v_beta_3461_; uint8_t v_proj_3462_; uint8_t v_zeta_3463_; uint8_t v_zetaDelta_3464_; uint8_t v_zetaUnused_3465_; uint8_t v_zetaHave_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3517_; 
v___x_3448_ = l_Lean_Meta_Context_config(v_a_3400_);
v_foApprox_3449_ = lean_ctor_get_uint8(v___x_3448_, 0);
v_ctxApprox_3450_ = lean_ctor_get_uint8(v___x_3448_, 1);
v_quasiPatternApprox_3451_ = lean_ctor_get_uint8(v___x_3448_, 2);
v_constApprox_3452_ = lean_ctor_get_uint8(v___x_3448_, 3);
v_isDefEqStuckEx_3453_ = lean_ctor_get_uint8(v___x_3448_, 4);
v_unificationHints_3454_ = lean_ctor_get_uint8(v___x_3448_, 5);
v_proofIrrelevance_3455_ = lean_ctor_get_uint8(v___x_3448_, 6);
v_assignSyntheticOpaque_3456_ = lean_ctor_get_uint8(v___x_3448_, 7);
v_offsetCnstrs_3457_ = lean_ctor_get_uint8(v___x_3448_, 8);
v_etaStruct_3458_ = lean_ctor_get_uint8(v___x_3448_, 10);
v_univApprox_3459_ = lean_ctor_get_uint8(v___x_3448_, 11);
v_iota_3460_ = lean_ctor_get_uint8(v___x_3448_, 12);
v_beta_3461_ = lean_ctor_get_uint8(v___x_3448_, 13);
v_proj_3462_ = lean_ctor_get_uint8(v___x_3448_, 14);
v_zeta_3463_ = lean_ctor_get_uint8(v___x_3448_, 15);
v_zetaDelta_3464_ = lean_ctor_get_uint8(v___x_3448_, 16);
v_zetaUnused_3465_ = lean_ctor_get_uint8(v___x_3448_, 17);
v_zetaHave_3466_ = lean_ctor_get_uint8(v___x_3448_, 18);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3468_ = v___x_3448_;
v_isShared_3469_ = v_isSharedCheck_3517_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v___x_3448_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3517_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
uint8_t v_trackZetaDelta_3470_; lean_object* v_zetaDeltaSet_3471_; lean_object* v_lctx_3472_; lean_object* v_localInstances_3473_; lean_object* v_defEqCtx_x3f_3474_; lean_object* v_synthPendingDepth_3475_; lean_object* v_canUnfold_x3f_3476_; uint8_t v_univApprox_3477_; uint8_t v_inTypeClassResolution_3478_; uint8_t v_cacheInferType_3479_; lean_object* v_config_3481_; 
v_trackZetaDelta_3470_ = lean_ctor_get_uint8(v_a_3400_, sizeof(void*)*7);
v_zetaDeltaSet_3471_ = lean_ctor_get(v_a_3400_, 1);
lean_inc(v_zetaDeltaSet_3471_);
v_lctx_3472_ = lean_ctor_get(v_a_3400_, 2);
lean_inc_ref(v_lctx_3472_);
v_localInstances_3473_ = lean_ctor_get(v_a_3400_, 3);
lean_inc_ref(v_localInstances_3473_);
v_defEqCtx_x3f_3474_ = lean_ctor_get(v_a_3400_, 4);
lean_inc(v_defEqCtx_x3f_3474_);
v_synthPendingDepth_3475_ = lean_ctor_get(v_a_3400_, 5);
lean_inc(v_synthPendingDepth_3475_);
v_canUnfold_x3f_3476_ = lean_ctor_get(v_a_3400_, 6);
lean_inc(v_canUnfold_x3f_3476_);
v_univApprox_3477_ = lean_ctor_get_uint8(v_a_3400_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3478_ = lean_ctor_get_uint8(v_a_3400_, sizeof(void*)*7 + 2);
v_cacheInferType_3479_ = lean_ctor_get_uint8(v_a_3400_, sizeof(void*)*7 + 3);
if (v_isShared_3469_ == 0)
{
v_config_3481_ = v___x_3468_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 0, v_foApprox_3449_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 1, v_ctxApprox_3450_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 2, v_quasiPatternApprox_3451_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 3, v_constApprox_3452_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 4, v_isDefEqStuckEx_3453_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 5, v_unificationHints_3454_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 6, v_proofIrrelevance_3455_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 7, v_assignSyntheticOpaque_3456_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 8, v_offsetCnstrs_3457_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 10, v_etaStruct_3458_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 11, v_univApprox_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 12, v_iota_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 13, v_beta_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 14, v_proj_3462_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 15, v_zeta_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 16, v_zetaDelta_3464_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 17, v_zetaUnused_3465_);
lean_ctor_set_uint8(v_reuseFailAlloc_3516_, 18, v_zetaHave_3466_);
v_config_3481_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
uint64_t v___x_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3508_; 
lean_ctor_set_uint8(v_config_3481_, 9, v___y_3447_);
v___x_3482_ = l_Lean_Meta_Context_configKey(v_a_3400_);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_a_3400_);
if (v_isSharedCheck_3508_ == 0)
{
lean_object* v_unused_3509_; lean_object* v_unused_3510_; lean_object* v_unused_3511_; lean_object* v_unused_3512_; lean_object* v_unused_3513_; lean_object* v_unused_3514_; lean_object* v_unused_3515_; 
v_unused_3509_ = lean_ctor_get(v_a_3400_, 6);
lean_dec(v_unused_3509_);
v_unused_3510_ = lean_ctor_get(v_a_3400_, 5);
lean_dec(v_unused_3510_);
v_unused_3511_ = lean_ctor_get(v_a_3400_, 4);
lean_dec(v_unused_3511_);
v_unused_3512_ = lean_ctor_get(v_a_3400_, 3);
lean_dec(v_unused_3512_);
v_unused_3513_ = lean_ctor_get(v_a_3400_, 2);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_a_3400_, 1);
lean_dec(v_unused_3514_);
v_unused_3515_ = lean_ctor_get(v_a_3400_, 0);
lean_dec(v_unused_3515_);
v___x_3484_ = v_a_3400_;
v_isShared_3485_ = v_isSharedCheck_3508_;
goto v_resetjp_3483_;
}
else
{
lean_dec(v_a_3400_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3508_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
uint64_t v___x_3486_; uint64_t v___x_3487_; uint64_t v___x_3488_; uint64_t v___x_3489_; uint64_t v_key_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3486_ = 2ULL;
v___x_3487_ = lean_uint64_shift_right(v___x_3482_, v___x_3486_);
v___x_3488_ = lean_uint64_shift_left(v___x_3487_, v___x_3486_);
v___x_3489_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3447_);
v_key_3490_ = lean_uint64_lor(v___x_3488_, v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3491_, 0, v_config_3481_);
lean_ctor_set_uint64(v___x_3491_, sizeof(void*)*1, v_key_3490_);
lean_inc(v_canUnfold_x3f_3476_);
lean_inc(v_synthPendingDepth_3475_);
lean_inc(v_defEqCtx_x3f_3474_);
lean_inc_ref(v_localInstances_3473_);
lean_inc_ref(v_lctx_3472_);
lean_inc(v_zetaDeltaSet_3471_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3491_);
v___x_3493_ = v___x_3484_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_zetaDeltaSet_3471_);
lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_lctx_3472_);
lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_localInstances_3473_);
lean_ctor_set(v_reuseFailAlloc_3507_, 4, v_defEqCtx_x3f_3474_);
lean_ctor_set(v_reuseFailAlloc_3507_, 5, v_synthPendingDepth_3475_);
lean_ctor_set(v_reuseFailAlloc_3507_, 6, v_canUnfold_x3f_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3507_, sizeof(void*)*7, v_trackZetaDelta_3470_);
lean_ctor_set_uint8(v_reuseFailAlloc_3507_, sizeof(void*)*7 + 1, v_univApprox_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3507_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3507_, sizeof(void*)*7 + 3, v_cacheInferType_3479_);
v___x_3493_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; uint8_t v_beta_3495_; 
v___x_3494_ = l_Lean_Meta_Context_config(v___x_3493_);
v_beta_3495_ = lean_ctor_get_uint8(v___x_3494_, 13);
if (v_beta_3495_ == 0)
{
lean_dec_ref(v___x_3494_);
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
uint8_t v_iota_3496_; 
v_iota_3496_ = lean_ctor_get_uint8(v___x_3494_, 12);
if (v_iota_3496_ == 0)
{
lean_dec_ref(v___x_3494_);
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
uint8_t v_zeta_3497_; 
v_zeta_3497_ = lean_ctor_get_uint8(v___x_3494_, 15);
if (v_zeta_3497_ == 0)
{
lean_dec_ref(v___x_3494_);
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
uint8_t v_zetaHave_3498_; 
v_zetaHave_3498_ = lean_ctor_get_uint8(v___x_3494_, 18);
if (v_zetaHave_3498_ == 0)
{
lean_dec_ref(v___x_3494_);
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
uint8_t v_zetaDelta_3499_; 
v_zetaDelta_3499_ = lean_ctor_get_uint8(v___x_3494_, 16);
if (v_zetaDelta_3499_ == 0)
{
lean_dec_ref(v___x_3494_);
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
uint8_t v_etaStruct_3500_; uint8_t v_proj_3501_; uint8_t v___x_3502_; uint8_t v___x_3503_; 
v_etaStruct_3500_ = lean_ctor_get_uint8(v___x_3494_, 10);
v_proj_3501_ = lean_ctor_get_uint8(v___x_3494_, 14);
lean_dec_ref(v___x_3494_);
v___x_3502_ = 2;
v___x_3503_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
uint8_t v___x_3504_; uint8_t v___x_3505_; 
v___x_3504_ = 0;
v___x_3505_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3500_, v___x_3504_);
if (v___x_3505_ == 0)
{
v___y_3406_ = v___y_3446_;
v___y_3407_ = v_localInstances_3473_;
v___y_3408_ = v_synthPendingDepth_3475_;
v___y_3409_ = v_inTypeClassResolution_3478_;
v___y_3410_ = v_univApprox_3477_;
v___y_3411_ = v___x_3493_;
v___y_3412_ = v_defEqCtx_x3f_3474_;
v___y_3413_ = v_canUnfold_x3f_3476_;
v___y_3414_ = v_lctx_3472_;
v___y_3415_ = v_cacheInferType_3479_;
v___y_3416_ = v_zetaDeltaSet_3471_;
v___y_3417_ = v_trackZetaDelta_3470_;
goto v___jp_3405_;
}
else
{
lean_object* v___x_3506_; 
lean_dec(v_canUnfold_x3f_3476_);
lean_dec(v_synthPendingDepth_3475_);
lean_dec(v_defEqCtx_x3f_3474_);
lean_dec_ref(v_localInstances_3473_);
lean_dec_ref(v_lctx_3472_);
lean_dec(v_zetaDeltaSet_3471_);
v___x_3506_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3399_, v___x_3493_, v_a_3401_, v___y_3446_, v_a_3403_);
lean_dec(v_a_3403_);
lean_dec_ref(v___y_3446_);
lean_dec(v_a_3401_);
lean_dec_ref(v___x_3493_);
return v___x_3506_;
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
v_resetjp_3534_:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = lean_nat_dec_eq(v_maxRecDepth_3522_, v___x_3547_);
if (v___x_3548_ == 0)
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_nat_dec_eq(v_currRecDepth_3521_, v_maxRecDepth_3522_);
if (v___x_3549_ == 0)
{
goto v___jp_3537_;
}
else
{
lean_object* v___x_3550_; 
lean_del_object(v___x_3535_);
lean_dec_ref(v_inheritedTraceOptions_3533_);
lean_dec(v_cancelTk_x3f_3531_);
lean_dec(v_currMacroScope_3529_);
lean_dec(v_quotContext_3528_);
lean_dec(v_maxHeartbeats_3527_);
lean_dec(v_initHeartbeats_3526_);
lean_dec(v_openDecls_3525_);
lean_dec(v_currNamespace_3524_);
lean_dec(v_maxRecDepth_3522_);
lean_dec(v_currRecDepth_3521_);
lean_dec_ref(v_options_3520_);
lean_dec_ref(v_fileMap_3519_);
lean_dec_ref(v_fileName_3518_);
lean_dec(v_a_3403_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec_ref(v_e_3399_);
v___x_3550_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3523_);
return v___x_3550_;
}
}
else
{
goto v___jp_3537_;
}
v___jp_3537_:
{
lean_object* v___x_3538_; uint8_t v_transparency_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3538_ = l_Lean_Meta_Context_config(v_a_3400_);
v_transparency_3539_ = lean_ctor_get_uint8(v___x_3538_, 9);
lean_dec_ref(v___x_3538_);
v___x_3540_ = lean_unsigned_to_nat(1u);
v___x_3541_ = lean_nat_add(v_currRecDepth_3521_, v___x_3540_);
lean_dec(v_currRecDepth_3521_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 3, v___x_3541_);
v___x_3543_ = v___x_3535_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_fileName_3518_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_fileMap_3519_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_options_3520_);
lean_ctor_set(v_reuseFailAlloc_3546_, 3, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3546_, 4, v_maxRecDepth_3522_);
lean_ctor_set(v_reuseFailAlloc_3546_, 5, v_ref_3523_);
lean_ctor_set(v_reuseFailAlloc_3546_, 6, v_currNamespace_3524_);
lean_ctor_set(v_reuseFailAlloc_3546_, 7, v_openDecls_3525_);
lean_ctor_set(v_reuseFailAlloc_3546_, 8, v_initHeartbeats_3526_);
lean_ctor_set(v_reuseFailAlloc_3546_, 9, v_maxHeartbeats_3527_);
lean_ctor_set(v_reuseFailAlloc_3546_, 10, v_quotContext_3528_);
lean_ctor_set(v_reuseFailAlloc_3546_, 11, v_currMacroScope_3529_);
lean_ctor_set(v_reuseFailAlloc_3546_, 12, v_cancelTk_x3f_3531_);
lean_ctor_set(v_reuseFailAlloc_3546_, 13, v_inheritedTraceOptions_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3546_, sizeof(void*)*14, v_diag_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3546_, sizeof(void*)*14 + 1, v_suppressElabErrors_3532_);
v___x_3543_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
uint8_t v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = 1;
v___x_3545_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3539_, v___x_3544_);
if (v___x_3545_ == 0)
{
v___y_3446_ = v___x_3543_;
v___y_3447_ = v_transparency_3539_;
goto v___jp_3445_;
}
else
{
v___y_3446_ = v___x_3543_;
v___y_3447_ = v___x_3544_;
goto v___jp_3445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = lean_infer_type(v_e_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
return v_res_3558_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3559_){
_start:
{
switch(lean_obj_tag(v_x_3559_))
{
case 0:
{
uint8_t v___x_3560_; 
v___x_3560_ = 1;
return v___x_3560_;
}
case 2:
{
lean_object* v_a_3561_; lean_object* v_a_3562_; uint8_t v___x_3563_; 
v_a_3561_ = lean_ctor_get(v_x_3559_, 0);
v_a_3562_ = lean_ctor_get(v_x_3559_, 1);
v___x_3563_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3561_);
if (v___x_3563_ == 0)
{
return v___x_3563_;
}
else
{
v_x_3559_ = v_a_3562_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3565_; 
v_a_3565_ = lean_ctor_get(v_x_3559_, 1);
v_x_3559_ = v_a_3565_;
goto _start;
}
default: 
{
uint8_t v___x_3567_; 
v___x_3567_ = 0;
return v___x_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3568_){
_start:
{
uint8_t v_res_3569_; lean_object* v_r_3570_; 
v_res_3569_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3568_);
lean_dec(v_x_3568_);
v_r_3570_ = lean_box(v_res_3569_);
return v_r_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v_mctx_3575_; lean_object* v___x_3576_; lean_object* v_fst_3577_; lean_object* v_snd_3578_; lean_object* v___x_3579_; lean_object* v_cache_3580_; lean_object* v_zetaDeltaFVarIds_3581_; lean_object* v_postponed_3582_; lean_object* v_diag_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3592_; 
v___x_3574_ = lean_st_ref_get(v___y_3572_);
v_mctx_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc_ref(v_mctx_3575_);
lean_dec(v___x_3574_);
v___x_3576_ = lean_instantiate_level_mvars(v_mctx_3575_, v_l_3571_);
v_fst_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_fst_3577_);
v_snd_3578_ = lean_ctor_get(v___x_3576_, 1);
lean_inc(v_snd_3578_);
lean_dec_ref(v___x_3576_);
v___x_3579_ = lean_st_ref_take(v___y_3572_);
v_cache_3580_ = lean_ctor_get(v___x_3579_, 1);
v_zetaDeltaFVarIds_3581_ = lean_ctor_get(v___x_3579_, 2);
v_postponed_3582_ = lean_ctor_get(v___x_3579_, 3);
v_diag_3583_ = lean_ctor_get(v___x_3579_, 4);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v___x_3579_, 0);
lean_dec(v_unused_3593_);
v___x_3585_ = v___x_3579_;
v_isShared_3586_ = v_isSharedCheck_3592_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_diag_3583_);
lean_inc(v_postponed_3582_);
lean_inc(v_zetaDeltaFVarIds_3581_);
lean_inc(v_cache_3580_);
lean_dec(v___x_3579_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3592_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v_fst_3577_);
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_fst_3577_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_cache_3580_);
lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_zetaDeltaFVarIds_3581_);
lean_ctor_set(v_reuseFailAlloc_3591_, 3, v_postponed_3582_);
lean_ctor_set(v_reuseFailAlloc_3591_, 4, v_diag_3583_);
v___x_3588_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_st_ref_set(v___y_3572_, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v_snd_3578_);
return v___x_3590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3594_, v___y_3595_);
lean_dec(v___y_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3598_, v___y_3600_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3612_, lean_object* v_x_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_){
_start:
{
switch(lean_obj_tag(v_x_3612_))
{
case 3:
{
lean_object* v_u_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v_u_3623_ = lean_ctor_get(v_x_3612_, 0);
lean_inc(v_u_3623_);
lean_dec_ref(v_x_3612_);
v___x_3624_ = lean_unsigned_to_nat(0u);
v___x_3625_ = lean_nat_dec_eq(v_x_3613_, v___x_3624_);
lean_dec(v_x_3613_);
if (v___x_3625_ == 0)
{
lean_dec(v_u_3623_);
goto v___jp_3619_;
}
else
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3623_, v_a_3615_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3637_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
uint8_t v___x_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3631_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3627_);
lean_dec(v_a_3627_);
v___x_3632_ = l_Bool_toLBool(v___x_3631_);
v___x_3633_ = lean_box(v___x_3632_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3633_);
v___x_3635_ = v___x_3629_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
v_a_3638_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3626_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3626_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3646_; lean_object* v_zero_3647_; uint8_t v_isZero_3648_; 
v_body_3646_ = lean_ctor_get(v_x_3612_, 2);
lean_inc_ref(v_body_3646_);
lean_dec_ref(v_x_3612_);
v_zero_3647_ = lean_unsigned_to_nat(0u);
v_isZero_3648_ = lean_nat_dec_eq(v_x_3613_, v_zero_3647_);
if (v_isZero_3648_ == 1)
{
uint8_t v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec_ref(v_body_3646_);
lean_dec(v_x_3613_);
v___x_3649_ = 0;
v___x_3650_ = lean_box(v___x_3649_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
else
{
lean_object* v_one_3652_; lean_object* v_n_3653_; 
v_one_3652_ = lean_unsigned_to_nat(1u);
v_n_3653_ = lean_nat_sub(v_x_3613_, v_one_3652_);
lean_dec(v_x_3613_);
v_x_3612_ = v_body_3646_;
v_x_3613_ = v_n_3653_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3655_; 
v_body_3655_ = lean_ctor_get(v_x_3612_, 3);
lean_inc_ref(v_body_3655_);
lean_dec_ref(v_x_3612_);
v_x_3612_ = v_body_3655_;
goto _start;
}
case 10:
{
lean_object* v_expr_3657_; 
v_expr_3657_ = lean_ctor_get(v_x_3612_, 1);
lean_inc_ref(v_expr_3657_);
lean_dec_ref(v_x_3612_);
v_x_3612_ = v_expr_3657_;
goto _start;
}
default: 
{
lean_dec(v_x_3613_);
lean_dec_ref(v_x_3612_);
goto v___jp_3619_;
}
}
v___jp_3619_:
{
uint8_t v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3620_ = 2;
v___x_3621_ = lean_box(v___x_3620_);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3659_, lean_object* v_x_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3659_, v_x_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3667_, lean_object* v_x_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
switch(lean_obj_tag(v_x_3667_))
{
case 4:
{
lean_object* v_declName_3674_; lean_object* v_us_3675_; lean_object* v___x_3676_; 
v_declName_3674_ = lean_ctor_get(v_x_3667_, 0);
lean_inc(v_declName_3674_);
v_us_3675_ = lean_ctor_get(v_x_3667_, 1);
lean_inc(v_us_3675_);
lean_dec_ref(v_x_3667_);
v___x_3676_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3674_, v_us_3675_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3677_, v_x_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3678_;
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_x_3668_);
v_a_3679_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3676_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3676_);
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
case 1:
{
lean_object* v_fvarId_3687_; lean_object* v___x_3688_; 
v_fvarId_3687_ = lean_ctor_get(v_x_3667_, 0);
lean_inc(v_fvarId_3687_);
lean_dec_ref(v_x_3667_);
v___x_3688_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3687_, v_a_3669_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___x_3688_);
v___x_3690_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3689_, v_x_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3690_;
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_x_3668_);
v_a_3691_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3688_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3688_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3699_; lean_object* v___x_3700_; 
v_mvarId_3699_ = lean_ctor_get(v_x_3667_, 0);
lean_inc(v_mvarId_3699_);
lean_dec_ref(v_x_3667_);
v___x_3700_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3699_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3701_, v_x_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3702_;
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_x_3668_);
v_a_3703_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3700_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3700_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
case 5:
{
lean_object* v_fn_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_fn_3711_ = lean_ctor_get(v_x_3667_, 0);
lean_inc_ref(v_fn_3711_);
lean_dec_ref(v_x_3667_);
v___x_3712_ = lean_unsigned_to_nat(1u);
v___x_3713_ = lean_nat_add(v_x_3668_, v___x_3712_);
lean_dec(v_x_3668_);
v_x_3667_ = v_fn_3711_;
v_x_3668_ = v___x_3713_;
goto _start;
}
case 10:
{
lean_object* v_expr_3715_; 
v_expr_3715_ = lean_ctor_get(v_x_3667_, 1);
lean_inc_ref(v_expr_3715_);
lean_dec_ref(v_x_3667_);
v_x_3667_ = v_expr_3715_;
goto _start;
}
case 8:
{
lean_object* v_body_3717_; 
v_body_3717_ = lean_ctor_get(v_x_3667_, 3);
lean_inc_ref(v_body_3717_);
lean_dec_ref(v_x_3667_);
v_x_3667_ = v_body_3717_;
goto _start;
}
case 6:
{
lean_object* v_body_3719_; lean_object* v_zero_3720_; uint8_t v_isZero_3721_; 
v_body_3719_ = lean_ctor_get(v_x_3667_, 2);
lean_inc_ref(v_body_3719_);
lean_dec_ref(v_x_3667_);
v_zero_3720_ = lean_unsigned_to_nat(0u);
v_isZero_3721_ = lean_nat_dec_eq(v_x_3668_, v_zero_3720_);
if (v_isZero_3721_ == 1)
{
uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref(v_body_3719_);
lean_dec(v_x_3668_);
v___x_3722_ = 0;
v___x_3723_ = lean_box(v___x_3722_);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v_one_3725_; lean_object* v_n_3726_; 
v_one_3725_ = lean_unsigned_to_nat(1u);
v_n_3726_ = lean_nat_sub(v_x_3668_, v_one_3725_);
lean_dec(v_x_3668_);
v_x_3667_ = v_body_3719_;
v_x_3668_ = v_n_3726_;
goto _start;
}
}
default: 
{
uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_x_3668_);
lean_dec_ref(v_x_3667_);
v___x_3728_ = 2;
v___x_3729_ = lean_box(v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3731_, lean_object* v_x_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3731_, v_x_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
switch(lean_obj_tag(v_x_3739_))
{
case 0:
{
uint8_t v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_dec_ref(v_x_3739_);
v___x_3745_ = 2;
v___x_3746_ = lean_box(v___x_3745_);
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
case 1:
{
lean_object* v_fvarId_3748_; lean_object* v___x_3749_; 
v_fvarId_3748_ = lean_ctor_get(v_x_3739_, 0);
lean_inc(v_fvarId_3748_);
lean_dec_ref(v_x_3739_);
v___x_3749_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3748_, v_a_3740_, v_a_3742_, v_a_3743_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref(v___x_3749_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v___x_3752_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3750_, v___x_3751_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v___x_3752_;
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_a_3753_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3749_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3749_);
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
case 2:
{
lean_object* v_mvarId_3761_; lean_object* v___x_3762_; 
v_mvarId_3761_ = lean_ctor_get(v_x_3739_, 0);
lean_inc(v_mvarId_3761_);
lean_dec_ref(v_x_3739_);
v___x_3762_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3761_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = lean_unsigned_to_nat(0u);
v___x_3765_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3763_, v___x_3764_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v___x_3765_;
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
v_a_3766_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3762_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3762_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
case 4:
{
lean_object* v_declName_3774_; lean_object* v_us_3775_; lean_object* v___x_3776_; 
v_declName_3774_ = lean_ctor_get(v_x_3739_, 0);
lean_inc(v_declName_3774_);
v_us_3775_ = lean_ctor_get(v_x_3739_, 1);
lean_inc(v_us_3775_);
lean_dec_ref(v_x_3739_);
v___x_3776_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3774_, v_us_3775_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3777_, v___x_3778_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v___x_3779_;
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v_a_3780_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3776_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3776_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
case 5:
{
lean_object* v_fn_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_fn_3788_ = lean_ctor_get(v_x_3739_, 0);
lean_inc_ref(v_fn_3788_);
lean_dec_ref(v_x_3739_);
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_3788_, v___x_3789_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v___x_3790_;
}
case 7:
{
lean_object* v_body_3791_; 
v_body_3791_ = lean_ctor_get(v_x_3739_, 2);
lean_inc_ref(v_body_3791_);
lean_dec_ref(v_x_3739_);
v_x_3739_ = v_body_3791_;
goto _start;
}
case 8:
{
lean_object* v_body_3793_; 
v_body_3793_ = lean_ctor_get(v_x_3739_, 3);
lean_inc_ref(v_body_3793_);
lean_dec_ref(v_x_3739_);
v_x_3739_ = v_body_3793_;
goto _start;
}
case 10:
{
lean_object* v_expr_3795_; 
v_expr_3795_ = lean_ctor_get(v_x_3739_, 1);
lean_inc_ref(v_expr_3795_);
lean_dec_ref(v_x_3739_);
v_x_3739_ = v_expr_3795_;
goto _start;
}
case 11:
{
uint8_t v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec_ref(v_x_3739_);
v___x_3797_ = 2;
v___x_3798_ = lean_box(v___x_3797_);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
default: 
{
uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec_ref(v_x_3739_);
v___x_3800_ = 0;
v___x_3801_ = lean_box(v___x_3800_);
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
return v___x_3802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_Meta_isPropQuick(v_x_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
lean_dec_ref(v_a_3804_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
lean_object* v___x_3816_; 
lean_inc_ref(v_e_3810_);
v___x_3816_ = l_Lean_Meta_isPropQuick(v_e_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3873_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3873_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3873_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
uint8_t v___x_3821_; 
v___x_3821_ = lean_unbox(v_a_3817_);
lean_dec(v_a_3817_);
switch(v___x_3821_)
{
case 0:
{
uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_dec_ref(v_e_3810_);
v___x_3822_ = 0;
v___x_3823_ = lean_box(v___x_3822_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3823_);
v___x_3825_ = v___x_3819_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
case 1:
{
uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
lean_dec_ref(v_e_3810_);
v___x_3827_ = 1;
v___x_3828_ = lean_box(v___x_3827_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3828_);
v___x_3830_ = v___x_3819_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
default: 
{
lean_object* v___x_3832_; 
lean_del_object(v___x_3819_);
lean_inc(v_a_3814_);
lean_inc_ref(v_a_3813_);
lean_inc(v_a_3812_);
lean_inc_ref(v_a_3811_);
v___x_3832_ = lean_infer_type(v_e_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3834_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v___x_3832_);
v___x_3834_ = l_Lean_Meta_whnfD(v_a_3833_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3856_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3856_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3856_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
if (lean_obj_tag(v_a_3835_) == 3)
{
lean_object* v_u_3839_; lean_object* v___x_3840_; lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3850_; 
lean_del_object(v___x_3837_);
v_u_3839_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_u_3839_);
lean_dec_ref(v_a_3835_);
v___x_3840_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3839_, v_a_3812_);
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3845_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3841_);
lean_dec(v_a_3841_);
v___x_3846_ = lean_box(v___x_3845_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3846_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
else
{
uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
lean_dec(v_a_3835_);
v___x_3851_ = 0;
v___x_3852_ = lean_box(v___x_3851_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3852_);
v___x_3854_ = v___x_3837_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
v_a_3857_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3834_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3834_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
v_a_3865_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3832_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3832_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_e_3810_);
v_a_3874_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3816_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3816_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Meta_isProp(v_e_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_3889_){
_start:
{
switch(lean_obj_tag(v_x_3889_))
{
case 0:
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_unsigned_to_nat(0u);
return v___x_3890_;
}
case 1:
{
lean_object* v___x_3891_; 
v___x_3891_ = lean_unsigned_to_nat(1u);
return v___x_3891_;
}
case 2:
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_unsigned_to_nat(2u);
return v___x_3892_;
}
default: 
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_unsigned_to_nat(3u);
return v___x_3893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_3894_);
lean_dec(v_x_3894_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_3896_, lean_object* v_k_3897_){
_start:
{
if (lean_obj_tag(v_t_3896_) == 3)
{
lean_object* v_idx_3898_; lean_object* v___x_3899_; 
v_idx_3898_ = lean_ctor_get(v_t_3896_, 0);
lean_inc(v_idx_3898_);
lean_dec_ref(v_t_3896_);
v___x_3899_ = lean_apply_1(v_k_3897_, v_idx_3898_);
return v___x_3899_;
}
else
{
lean_dec(v_t_3896_);
return v_k_3897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_3900_, lean_object* v_ctorIdx_3901_, lean_object* v_t_3902_, lean_object* v_h_3903_, lean_object* v_k_3904_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3902_, v_k_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_3906_, lean_object* v_ctorIdx_3907_, lean_object* v_t_3908_, lean_object* v_h_3909_, lean_object* v_k_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_3906_, v_ctorIdx_3907_, v_t_3908_, v_h_3909_, v_k_3910_);
lean_dec(v_ctorIdx_3907_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_3912_, lean_object* v_false_3913_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3912_, v_false_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_3915_, lean_object* v_t_3916_, lean_object* v_h_3917_, lean_object* v_false_3918_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3916_, v_false_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_3920_, lean_object* v_true_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3920_, v_true_3921_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_3923_, lean_object* v_t_3924_, lean_object* v_h_3925_, lean_object* v_true_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3924_, v_true_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_3928_, lean_object* v_undef_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3928_, v_undef_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_3931_, lean_object* v_t_3932_, lean_object* v_h_3933_, lean_object* v_undef_3934_){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3932_, v_undef_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_3936_, lean_object* v_bvar_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3936_, v_bvar_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_3939_, lean_object* v_t_3940_, lean_object* v_h_3941_, lean_object* v_bvar_3942_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3940_, v_bvar_3942_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_3944_){
_start:
{
switch(v_x_3944_)
{
case 0:
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_box(0);
return v___x_3945_;
}
case 1:
{
lean_object* v___x_3946_; 
v___x_3946_ = lean_box(1);
return v___x_3946_;
}
default: 
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_box(2);
return v___x_3947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_3948_){
_start:
{
uint8_t v_x_25__boxed_3949_; lean_object* v_res_3950_; 
v_x_25__boxed_3949_ = lean_unbox(v_x_3948_);
v_res_3950_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_3949_);
return v_res_3950_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_3951_){
_start:
{
switch(lean_obj_tag(v_x_3951_))
{
case 0:
{
uint8_t v___x_3952_; 
v___x_3952_ = 0;
return v___x_3952_;
}
case 1:
{
uint8_t v___x_3953_; 
v___x_3953_ = 1;
return v___x_3953_;
}
default: 
{
uint8_t v___x_3954_; 
v___x_3954_ = 2;
return v___x_3954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_3955_){
_start:
{
uint8_t v_res_3956_; lean_object* v_r_3957_; 
v_res_3956_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_3955_);
lean_dec(v_x_3955_);
v_r_3957_ = lean_box(v_res_3956_);
return v_r_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_3959_){
_start:
{
switch(lean_obj_tag(v_e_3959_))
{
case 3:
{
lean_object* v_u_3960_; uint8_t v___x_3961_; 
v_u_3960_ = lean_ctor_get(v_e_3959_, 0);
v___x_3961_ = l_Lean_Level_isNeverZero(v_u_3960_);
if (v___x_3961_ == 0)
{
uint8_t v___x_3962_; 
v___x_3962_ = l_Lean_Level_isZero(v_u_3960_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_box(2);
return v___x_3963_;
}
else
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_box(1);
return v___x_3964_;
}
}
else
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_box(0);
return v___x_3965_;
}
}
case 5:
{
lean_object* v_fn_3966_; 
v_fn_3966_ = lean_ctor_get(v_e_3959_, 0);
if (lean_obj_tag(v_fn_3966_) == 4)
{
lean_object* v_declName_3967_; 
v_declName_3967_ = lean_ctor_get(v_fn_3966_, 0);
if (lean_obj_tag(v_declName_3967_) == 1)
{
lean_object* v_pre_3968_; 
v_pre_3968_ = lean_ctor_get(v_declName_3967_, 0);
if (lean_obj_tag(v_pre_3968_) == 0)
{
lean_object* v_arg_3969_; lean_object* v_str_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v_arg_3969_ = lean_ctor_get(v_e_3959_, 1);
v_str_3970_ = lean_ctor_get(v_declName_3967_, 1);
v___x_3971_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_3972_ = lean_string_dec_eq(v_str_3970_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_box(2);
return v___x_3973_;
}
else
{
v_e_3959_ = v_arg_3969_;
goto _start;
}
}
else
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_box(2);
return v___x_3975_;
}
}
else
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_box(2);
return v___x_3976_;
}
}
else
{
lean_object* v___x_3977_; 
v___x_3977_ = lean_box(2);
return v___x_3977_;
}
}
default: 
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_box(2);
return v___x_3978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_3979_);
lean_dec_ref(v_e_3979_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_3981_, lean_object* v_binderType_3982_){
_start:
{
if (lean_obj_tag(v_r_3981_) == 3)
{
lean_object* v_idx_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3995_; 
v_idx_3983_ = lean_ctor_get(v_r_3981_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_r_3981_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3985_ = v_r_3981_;
v_isShared_3986_ = v_isSharedCheck_3995_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_idx_3983_);
lean_dec(v_r_3981_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3995_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v_zero_3987_; uint8_t v_isZero_3988_; 
v_zero_3987_ = lean_unsigned_to_nat(0u);
v_isZero_3988_ = lean_nat_dec_eq(v_idx_3983_, v_zero_3987_);
if (v_isZero_3988_ == 1)
{
lean_object* v___x_3989_; 
lean_del_object(v___x_3985_);
lean_dec(v_idx_3983_);
v___x_3989_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_3982_);
return v___x_3989_;
}
else
{
lean_object* v_one_3990_; lean_object* v_n_3991_; lean_object* v___x_3993_; 
v_one_3990_ = lean_unsigned_to_nat(1u);
v_n_3991_ = lean_nat_sub(v_idx_3983_, v_one_3990_);
lean_dec(v_idx_3983_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v_n_3991_);
v___x_3993_ = v___x_3985_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_n_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
return v_r_3981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_3996_, lean_object* v_binderType_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_3996_, v_binderType_3997_);
lean_dec_ref(v_binderType_3997_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_3999_, lean_object* v_x_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_type_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; 
switch(lean_obj_tag(v_x_3999_))
{
case 7:
{
lean_object* v_binderType_4034_; lean_object* v_body_4035_; lean_object* v_zero_4036_; uint8_t v_isZero_4037_; 
v_binderType_4034_ = lean_ctor_get(v_x_3999_, 1);
v_body_4035_ = lean_ctor_get(v_x_3999_, 2);
v_zero_4036_ = lean_unsigned_to_nat(0u);
v_isZero_4037_ = lean_nat_dec_eq(v_x_4000_, v_zero_4036_);
if (v_isZero_4037_ == 1)
{
v_type_4007_ = v_x_3999_;
v___y_4008_ = v_a_4001_;
v___y_4009_ = v_a_4002_;
v___y_4010_ = v_a_4003_;
v___y_4011_ = v_a_4004_;
goto v___jp_4006_;
}
else
{
lean_object* v_one_4038_; lean_object* v_n_4039_; lean_object* v___x_4040_; 
lean_inc_ref(v_body_4035_);
lean_inc_ref(v_binderType_4034_);
lean_dec_ref(v_x_3999_);
v_one_4038_ = lean_unsigned_to_nat(1u);
v_n_4039_ = lean_nat_sub(v_x_4000_, v_one_4038_);
v___x_4040_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4035_, v_n_4039_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
lean_dec(v_n_4039_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4049_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4049_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4049_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4041_, v_binderType_4034_);
lean_dec_ref(v_binderType_4034_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4045_);
v___x_4047_ = v___x_4043_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
else
{
lean_dec_ref(v_binderType_4034_);
return v___x_4040_;
}
}
}
case 8:
{
lean_object* v_type_4050_; lean_object* v_body_4051_; lean_object* v___x_4052_; 
v_type_4050_ = lean_ctor_get(v_x_3999_, 1);
lean_inc_ref(v_type_4050_);
v_body_4051_ = lean_ctor_get(v_x_3999_, 3);
lean_inc_ref(v_body_4051_);
lean_dec_ref(v_x_3999_);
v___x_4052_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4051_, v_x_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4061_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4057_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4053_, v_type_4050_);
lean_dec_ref(v_type_4050_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4057_);
v___x_4059_ = v___x_4055_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
else
{
lean_dec_ref(v_type_4050_);
return v___x_4052_;
}
}
case 10:
{
lean_object* v_expr_4062_; 
v_expr_4062_ = lean_ctor_get(v_x_3999_, 1);
lean_inc_ref(v_expr_4062_);
lean_dec_ref(v_x_3999_);
v_x_3999_ = v_expr_4062_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_deBruijnIndex_4064_ = lean_ctor_get(v_x_3999_, 0);
lean_inc(v_deBruijnIndex_4064_);
lean_dec_ref(v_x_3999_);
v___x_4065_ = lean_unsigned_to_nat(0u);
v___x_4066_ = lean_nat_dec_eq(v_x_4000_, v___x_4065_);
if (v___x_4066_ == 0)
{
lean_dec(v_deBruijnIndex_4064_);
goto v___jp_4031_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4067_, 0, v_deBruijnIndex_4064_);
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
default: 
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = lean_nat_dec_eq(v_x_4000_, v___x_4069_);
if (v___x_4070_ == 0)
{
lean_dec_ref(v_x_3999_);
goto v___jp_4031_;
}
else
{
v_type_4007_ = v_x_3999_;
v___y_4008_ = v_a_4001_;
v___y_4009_ = v_a_4002_;
v___y_4010_ = v_a_4003_;
v___y_4011_ = v_a_4004_;
goto v___jp_4006_;
}
}
}
v___jp_4006_:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_Meta_isPropQuick(v_type_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4022_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
uint8_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4017_ = lean_unbox(v_a_4013_);
lean_dec(v_a_4013_);
v___x_4018_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4017_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4018_);
v___x_4020_ = v___x_4015_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
v_a_4023_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4012_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4012_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
v___jp_4031_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_box(2);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4071_, lean_object* v_x_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4071_, v_x_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_x_4072_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4079_, lean_object* v_n_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4079_, v_n_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4096_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4096_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4091_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4087_);
lean_dec(v_a_4087_);
v___x_4092_ = lean_box(v___x_4091_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4092_);
v___x_4094_ = v___x_4089_;
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
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
v_a_4097_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4086_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4086_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4105_, lean_object* v_n_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4105_, v_n_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
lean_dec(v_a_4110_);
lean_dec_ref(v_a_4109_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
lean_dec(v_n_4106_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4113_, lean_object* v_x_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
switch(lean_obj_tag(v_x_4113_))
{
case 4:
{
lean_object* v_declName_4120_; lean_object* v_us_4121_; lean_object* v___x_4122_; 
v_declName_4120_ = lean_ctor_get(v_x_4113_, 0);
lean_inc(v_declName_4120_);
v_us_4121_ = lean_ctor_get(v_x_4113_, 1);
lean_inc(v_us_4121_);
lean_dec_ref(v_x_4113_);
v___x_4122_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4120_, v_us_4121_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref(v___x_4122_);
v___x_4124_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4123_, v_x_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
lean_dec(v_x_4114_);
return v___x_4124_;
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v_x_4114_);
v_a_4125_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4122_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4122_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4133_; lean_object* v___x_4134_; 
v_fvarId_4133_ = lean_ctor_get(v_x_4113_, 0);
lean_inc(v_fvarId_4133_);
lean_dec_ref(v_x_4113_);
v___x_4134_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4133_, v_a_4115_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4136_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref(v___x_4134_);
v___x_4136_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4135_, v_x_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
lean_dec(v_x_4114_);
return v___x_4136_;
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v_x_4114_);
v_a_4137_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4134_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4134_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4145_; lean_object* v___x_4146_; 
v_mvarId_4145_ = lean_ctor_get(v_x_4113_, 0);
lean_inc(v_mvarId_4145_);
lean_dec_ref(v_x_4113_);
v___x_4146_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4145_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4148_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref(v___x_4146_);
v___x_4148_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4147_, v_x_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
lean_dec(v_x_4114_);
return v___x_4148_;
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec(v_x_4114_);
v_a_4149_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4146_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4146_);
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
case 5:
{
lean_object* v_fn_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_fn_4157_ = lean_ctor_get(v_x_4113_, 0);
lean_inc_ref(v_fn_4157_);
lean_dec_ref(v_x_4113_);
v___x_4158_ = lean_unsigned_to_nat(1u);
v___x_4159_ = lean_nat_add(v_x_4114_, v___x_4158_);
lean_dec(v_x_4114_);
v_x_4113_ = v_fn_4157_;
v_x_4114_ = v___x_4159_;
goto _start;
}
case 10:
{
lean_object* v_expr_4161_; 
v_expr_4161_ = lean_ctor_get(v_x_4113_, 1);
lean_inc_ref(v_expr_4161_);
lean_dec_ref(v_x_4113_);
v_x_4113_ = v_expr_4161_;
goto _start;
}
case 8:
{
lean_object* v_body_4163_; 
v_body_4163_ = lean_ctor_get(v_x_4113_, 3);
lean_inc_ref(v_body_4163_);
lean_dec_ref(v_x_4113_);
v_x_4113_ = v_body_4163_;
goto _start;
}
case 6:
{
lean_object* v_body_4165_; lean_object* v_zero_4166_; uint8_t v_isZero_4167_; 
v_body_4165_ = lean_ctor_get(v_x_4113_, 2);
lean_inc_ref(v_body_4165_);
lean_dec_ref(v_x_4113_);
v_zero_4166_ = lean_unsigned_to_nat(0u);
v_isZero_4167_ = lean_nat_dec_eq(v_x_4114_, v_zero_4166_);
if (v_isZero_4167_ == 1)
{
lean_object* v___x_4168_; 
lean_dec(v_x_4114_);
v___x_4168_ = l_Lean_Meta_isProofQuick(v_body_4165_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_);
return v___x_4168_;
}
else
{
lean_object* v_one_4169_; lean_object* v_n_4170_; 
v_one_4169_ = lean_unsigned_to_nat(1u);
v_n_4170_ = lean_nat_sub(v_x_4114_, v_one_4169_);
lean_dec(v_x_4114_);
v_x_4113_ = v_body_4165_;
v_x_4114_ = v_n_4170_;
goto _start;
}
}
default: 
{
uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec(v_x_4114_);
lean_dec_ref(v_x_4113_);
v___x_4172_ = 2;
v___x_4173_ = lean_box(v___x_4172_);
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
switch(lean_obj_tag(v_x_4175_))
{
case 0:
{
uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v_x_4175_);
v___x_4181_ = 2;
v___x_4182_ = lean_box(v___x_4181_);
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
return v___x_4183_;
}
case 1:
{
lean_object* v_fvarId_4184_; lean_object* v___x_4185_; 
v_fvarId_4184_ = lean_ctor_get(v_x_4175_, 0);
lean_inc(v_fvarId_4184_);
lean_dec_ref(v_x_4175_);
v___x_4185_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4184_, v_a_4176_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref(v___x_4185_);
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4186_, v___x_4187_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
return v___x_4188_;
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
v_a_4189_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4185_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4185_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4197_; lean_object* v___x_4198_; 
v_mvarId_4197_ = lean_ctor_get(v_x_4175_, 0);
lean_inc(v_mvarId_4197_);
lean_dec_ref(v_x_4175_);
v___x_4198_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4197_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_unsigned_to_nat(0u);
v___x_4201_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4199_, v___x_4200_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
return v___x_4201_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
v_a_4202_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4198_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4198_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
case 4:
{
lean_object* v_declName_4210_; lean_object* v_us_4211_; lean_object* v___x_4212_; 
v_declName_4210_ = lean_ctor_get(v_x_4175_, 0);
lean_inc(v_declName_4210_);
v_us_4211_ = lean_ctor_get(v_x_4175_, 1);
lean_inc(v_us_4211_);
lean_dec_ref(v_x_4175_);
v___x_4212_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4210_, v_us_4211_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref(v___x_4212_);
v___x_4214_ = lean_unsigned_to_nat(0u);
v___x_4215_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4213_, v___x_4214_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
return v___x_4215_;
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
v_a_4216_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4212_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4212_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
case 5:
{
lean_object* v_fn_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_fn_4224_ = lean_ctor_get(v_x_4175_, 0);
lean_inc_ref(v_fn_4224_);
lean_dec_ref(v_x_4175_);
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4224_, v___x_4225_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
return v___x_4226_;
}
case 6:
{
lean_object* v_body_4227_; 
v_body_4227_ = lean_ctor_get(v_x_4175_, 2);
lean_inc_ref(v_body_4227_);
lean_dec_ref(v_x_4175_);
v_x_4175_ = v_body_4227_;
goto _start;
}
case 8:
{
lean_object* v_body_4229_; 
v_body_4229_ = lean_ctor_get(v_x_4175_, 3);
lean_inc_ref(v_body_4229_);
lean_dec_ref(v_x_4175_);
v_x_4175_ = v_body_4229_;
goto _start;
}
case 10:
{
lean_object* v_expr_4231_; 
v_expr_4231_ = lean_ctor_get(v_x_4175_, 1);
lean_inc_ref(v_expr_4231_);
lean_dec_ref(v_x_4175_);
v_x_4175_ = v_expr_4231_;
goto _start;
}
case 11:
{
uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_dec_ref(v_x_4175_);
v___x_4233_ = 2;
v___x_4234_ = lean_box(v___x_4233_);
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
return v___x_4235_;
}
default: 
{
uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_dec_ref(v_x_4175_);
v___x_4236_ = 0;
v___x_4237_ = lean_box(v___x_4236_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_Meta_isProofQuick(v_x_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4240_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4246_, lean_object* v_x_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4246_, v_x_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
lean_dec(v_a_4251_);
lean_dec_ref(v_a_4250_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v___x_4260_; 
lean_inc_ref(v_e_4254_);
v___x_4260_ = l_Lean_Meta_isProofQuick(v_e_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4287_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4263_ = v___x_4260_;
v_isShared_4264_ = v_isSharedCheck_4287_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4287_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
uint8_t v___x_4265_; 
v___x_4265_ = lean_unbox(v_a_4261_);
lean_dec(v_a_4261_);
switch(v___x_4265_)
{
case 0:
{
uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4269_; 
lean_dec_ref(v_e_4254_);
v___x_4266_ = 0;
v___x_4267_ = lean_box(v___x_4266_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4267_);
v___x_4269_ = v___x_4263_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
case 1:
{
uint8_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; 
lean_dec_ref(v_e_4254_);
v___x_4271_ = 1;
v___x_4272_ = lean_box(v___x_4271_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4272_);
v___x_4274_ = v___x_4263_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
default: 
{
lean_object* v___x_4276_; 
lean_del_object(v___x_4263_);
lean_inc(v_a_4258_);
lean_inc_ref(v_a_4257_);
lean_inc(v_a_4256_);
lean_inc_ref(v_a_4255_);
v___x_4276_ = lean_infer_type(v_e_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = l_Lean_Meta_isProp(v_a_4277_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
return v___x_4278_;
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4276_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4276_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v_e_4254_);
v_a_4288_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4260_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4260_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_Meta_isProof(v_e_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4303_, lean_object* v_x_4304_){
_start:
{
switch(lean_obj_tag(v_x_4303_))
{
case 3:
{
lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4310_ = lean_unsigned_to_nat(0u);
v___x_4311_ = lean_nat_dec_eq(v_x_4304_, v___x_4310_);
lean_dec(v_x_4304_);
if (v___x_4311_ == 0)
{
goto v___jp_4306_;
}
else
{
uint8_t v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4312_ = 1;
v___x_4313_ = lean_box(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
return v___x_4314_;
}
}
case 7:
{
lean_object* v_body_4315_; lean_object* v_zero_4316_; uint8_t v_isZero_4317_; 
v_body_4315_ = lean_ctor_get(v_x_4303_, 2);
v_zero_4316_ = lean_unsigned_to_nat(0u);
v_isZero_4317_ = lean_nat_dec_eq(v_x_4304_, v_zero_4316_);
if (v_isZero_4317_ == 1)
{
uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
lean_dec(v_x_4304_);
v___x_4318_ = 0;
v___x_4319_ = lean_box(v___x_4318_);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
else
{
lean_object* v_one_4321_; lean_object* v_n_4322_; 
v_one_4321_ = lean_unsigned_to_nat(1u);
v_n_4322_ = lean_nat_sub(v_x_4304_, v_one_4321_);
lean_dec(v_x_4304_);
v_x_4303_ = v_body_4315_;
v_x_4304_ = v_n_4322_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4324_; 
v_body_4324_ = lean_ctor_get(v_x_4303_, 3);
v_x_4303_ = v_body_4324_;
goto _start;
}
case 10:
{
lean_object* v_expr_4326_; 
v_expr_4326_ = lean_ctor_get(v_x_4303_, 1);
v_x_4303_ = v_expr_4326_;
goto _start;
}
default: 
{
lean_dec(v_x_4304_);
goto v___jp_4306_;
}
}
v___jp_4306_:
{
uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = 2;
v___x_4308_ = lean_box(v___x_4307_);
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4328_, lean_object* v_x_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4328_, v_x_4329_);
lean_dec_ref(v_x_4328_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4332_, lean_object* v_x_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4332_, v_x_4333_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4340_, lean_object* v_x_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4340_, v_x_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
lean_dec_ref(v_x_4340_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4348_, lean_object* v_x_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
switch(lean_obj_tag(v_x_4348_))
{
case 4:
{
lean_object* v_declName_4355_; lean_object* v_us_4356_; lean_object* v___x_4357_; 
v_declName_4355_ = lean_ctor_get(v_x_4348_, 0);
lean_inc(v_declName_4355_);
v_us_4356_ = lean_ctor_get(v_x_4348_, 1);
lean_inc(v_us_4356_);
lean_dec_ref(v_x_4348_);
v___x_4357_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4355_, v_us_4356_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref(v___x_4357_);
v___x_4359_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4358_, v_x_4349_);
lean_dec(v_a_4358_);
return v___x_4359_;
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v_x_4349_);
v_a_4360_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4357_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4357_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4368_; lean_object* v___x_4369_; 
v_fvarId_4368_ = lean_ctor_get(v_x_4348_, 0);
lean_inc(v_fvarId_4368_);
lean_dec_ref(v_x_4348_);
v___x_4369_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4368_, v_a_4350_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref(v___x_4369_);
v___x_4371_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4370_, v_x_4349_);
lean_dec(v_a_4370_);
return v___x_4371_;
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_x_4349_);
v_a_4372_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4369_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4369_);
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
case 2:
{
lean_object* v_mvarId_4380_; lean_object* v___x_4381_; 
v_mvarId_4380_ = lean_ctor_get(v_x_4348_, 0);
lean_inc(v_mvarId_4380_);
lean_dec_ref(v_x_4348_);
v___x_4381_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4380_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4383_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref(v___x_4381_);
v___x_4383_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4382_, v_x_4349_);
lean_dec(v_a_4382_);
return v___x_4383_;
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
lean_dec(v_x_4349_);
v_a_4384_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4381_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4381_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
case 5:
{
lean_object* v_fn_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v_fn_4392_ = lean_ctor_get(v_x_4348_, 0);
lean_inc_ref(v_fn_4392_);
lean_dec_ref(v_x_4348_);
v___x_4393_ = lean_unsigned_to_nat(1u);
v___x_4394_ = lean_nat_add(v_x_4349_, v___x_4393_);
lean_dec(v_x_4349_);
v_x_4348_ = v_fn_4392_;
v_x_4349_ = v___x_4394_;
goto _start;
}
case 10:
{
lean_object* v_expr_4396_; 
v_expr_4396_ = lean_ctor_get(v_x_4348_, 1);
lean_inc_ref(v_expr_4396_);
lean_dec_ref(v_x_4348_);
v_x_4348_ = v_expr_4396_;
goto _start;
}
case 8:
{
lean_object* v_body_4398_; 
v_body_4398_ = lean_ctor_get(v_x_4348_, 3);
lean_inc_ref(v_body_4398_);
lean_dec_ref(v_x_4348_);
v_x_4348_ = v_body_4398_;
goto _start;
}
case 6:
{
lean_object* v_body_4400_; lean_object* v_zero_4401_; uint8_t v_isZero_4402_; 
v_body_4400_ = lean_ctor_get(v_x_4348_, 2);
lean_inc_ref(v_body_4400_);
lean_dec_ref(v_x_4348_);
v_zero_4401_ = lean_unsigned_to_nat(0u);
v_isZero_4402_ = lean_nat_dec_eq(v_x_4349_, v_zero_4401_);
if (v_isZero_4402_ == 1)
{
uint8_t v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_dec_ref(v_body_4400_);
lean_dec(v_x_4349_);
v___x_4403_ = 0;
v___x_4404_ = lean_box(v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
return v___x_4405_;
}
else
{
lean_object* v_one_4406_; lean_object* v_n_4407_; 
v_one_4406_ = lean_unsigned_to_nat(1u);
v_n_4407_ = lean_nat_sub(v_x_4349_, v_one_4406_);
lean_dec(v_x_4349_);
v_x_4348_ = v_body_4400_;
v_x_4349_ = v_n_4407_;
goto _start;
}
}
default: 
{
uint8_t v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec(v_x_4349_);
lean_dec_ref(v_x_4348_);
v___x_4409_ = 2;
v___x_4410_ = lean_box(v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
return v___x_4411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4412_, lean_object* v_x_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4412_, v_x_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_a_4415_);
lean_dec_ref(v_a_4414_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
switch(lean_obj_tag(v_x_4420_))
{
case 1:
{
lean_object* v_fvarId_4426_; lean_object* v___x_4427_; 
v_fvarId_4426_ = lean_ctor_get(v_x_4420_, 0);
lean_inc(v_fvarId_4426_);
lean_dec_ref(v_x_4420_);
v___x_4427_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4426_, v_a_4421_, v_a_4423_, v_a_4424_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref(v___x_4427_);
v___x_4429_ = lean_unsigned_to_nat(0u);
v___x_4430_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4428_, v___x_4429_);
lean_dec(v_a_4428_);
return v___x_4430_;
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
v_a_4431_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4427_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4427_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4439_; lean_object* v___x_4440_; 
v_mvarId_4439_ = lean_ctor_get(v_x_4420_, 0);
lean_inc(v_mvarId_4439_);
lean_dec_ref(v_x_4420_);
v___x_4440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4439_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref(v___x_4440_);
v___x_4442_ = lean_unsigned_to_nat(0u);
v___x_4443_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4441_, v___x_4442_);
lean_dec(v_a_4441_);
return v___x_4443_;
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
v_a_4444_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4440_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4440_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
case 3:
{
uint8_t v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_dec_ref(v_x_4420_);
v___x_4452_ = 1;
v___x_4453_ = lean_box(v___x_4452_);
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
case 4:
{
lean_object* v_declName_4455_; lean_object* v_us_4456_; lean_object* v___x_4457_; 
v_declName_4455_ = lean_ctor_get(v_x_4420_, 0);
lean_inc(v_declName_4455_);
v_us_4456_ = lean_ctor_get(v_x_4420_, 1);
lean_inc(v_us_4456_);
lean_dec_ref(v_x_4420_);
v___x_4457_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4455_, v_us_4456_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
lean_dec_ref(v___x_4457_);
v___x_4459_ = lean_unsigned_to_nat(0u);
v___x_4460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4458_, v___x_4459_);
lean_dec(v_a_4458_);
return v___x_4460_;
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
v_a_4461_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4457_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4457_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
case 5:
{
lean_object* v_fn_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_fn_4469_ = lean_ctor_get(v_x_4420_, 0);
lean_inc_ref(v_fn_4469_);
lean_dec_ref(v_x_4420_);
v___x_4470_ = lean_unsigned_to_nat(1u);
v___x_4471_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4469_, v___x_4470_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
return v___x_4471_;
}
case 6:
{
uint8_t v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_dec_ref(v_x_4420_);
v___x_4472_ = 0;
v___x_4473_ = lean_box(v___x_4472_);
v___x_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
return v___x_4474_;
}
case 7:
{
uint8_t v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
lean_dec_ref(v_x_4420_);
v___x_4475_ = 1;
v___x_4476_ = lean_box(v___x_4475_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
case 8:
{
lean_object* v_body_4478_; 
v_body_4478_ = lean_ctor_get(v_x_4420_, 3);
lean_inc_ref(v_body_4478_);
lean_dec_ref(v_x_4420_);
v_x_4420_ = v_body_4478_;
goto _start;
}
case 9:
{
uint8_t v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_dec_ref(v_x_4420_);
v___x_4480_ = 0;
v___x_4481_ = lean_box(v___x_4480_);
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
return v___x_4482_;
}
case 10:
{
lean_object* v_expr_4483_; 
v_expr_4483_ = lean_ctor_get(v_x_4420_, 1);
lean_inc_ref(v_expr_4483_);
lean_dec_ref(v_x_4420_);
v_x_4420_ = v_expr_4483_;
goto _start;
}
default: 
{
uint8_t v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_dec_ref(v_x_4420_);
v___x_4485_ = 2;
v___x_4486_ = lean_box(v___x_4485_);
v___x_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
return v___x_4487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Meta_isTypeQuick(v_x_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v___x_4501_; 
lean_inc_ref(v_e_4495_);
v___x_4501_ = l_Lean_Meta_isTypeQuick(v_e_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4551_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4551_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4551_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
uint8_t v___x_4506_; 
v___x_4506_ = lean_unbox(v_a_4502_);
lean_dec(v_a_4502_);
switch(v___x_4506_)
{
case 0:
{
uint8_t v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
lean_dec_ref(v_e_4495_);
v___x_4507_ = 0;
v___x_4508_ = lean_box(v___x_4507_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___x_4508_);
v___x_4510_ = v___x_4504_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
case 1:
{
uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; 
lean_dec_ref(v_e_4495_);
v___x_4512_ = 1;
v___x_4513_ = lean_box(v___x_4512_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___x_4513_);
v___x_4515_ = v___x_4504_;
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
default: 
{
lean_object* v___x_4517_; 
lean_del_object(v___x_4504_);
lean_inc(v_a_4499_);
lean_inc_ref(v_a_4498_);
lean_inc(v_a_4497_);
lean_inc_ref(v_a_4496_);
v___x_4517_ = lean_infer_type(v_e_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref(v___x_4517_);
v___x_4519_ = l_Lean_Meta_whnfD(v_a_4518_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4534_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4522_ = v___x_4519_;
v_isShared_4523_ = v_isSharedCheck_4534_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4519_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4534_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
if (lean_obj_tag(v_a_4520_) == 3)
{
uint8_t v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4527_; 
lean_dec_ref(v_a_4520_);
v___x_4524_ = 1;
v___x_4525_ = lean_box(v___x_4524_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4525_);
v___x_4527_ = v___x_4522_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4525_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
else
{
uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; 
lean_dec(v_a_4520_);
v___x_4529_ = 0;
v___x_4530_ = lean_box(v___x_4529_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4530_);
v___x_4532_ = v___x_4522_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
v_a_4535_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4519_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4519_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
v_a_4543_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4517_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4517_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec_ref(v_e_4495_);
v_a_4552_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4501_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4501_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Meta_isType(v_e_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4567_){
_start:
{
switch(lean_obj_tag(v_x_4567_))
{
case 7:
{
lean_object* v_body_4568_; 
v_body_4568_ = lean_ctor_get(v_x_4567_, 2);
v_x_4567_ = v_body_4568_;
goto _start;
}
case 3:
{
lean_object* v_u_4570_; lean_object* v___x_4571_; 
v_u_4570_ = lean_ctor_get(v_x_4567_, 0);
lean_inc(v_u_4570_);
v___x_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4571_, 0, v_u_4570_);
return v___x_4571_;
}
default: 
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_box(0);
return v___x_4572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4573_);
lean_dec_ref(v_x_4573_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4575_, lean_object* v_body_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4575_, v_body_4576_, v_x_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4586_, lean_object* v_xs_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
switch(lean_obj_tag(v_type_4586_))
{
case 3:
{
lean_object* v_u_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
lean_dec_ref(v_xs_4587_);
v_u_4593_ = lean_ctor_get(v_type_4586_, 0);
lean_inc(v_u_4593_);
lean_dec_ref(v_type_4586_);
v___x_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4594_, 0, v_u_4593_);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
case 7:
{
lean_object* v_binderName_4596_; lean_object* v_binderType_4597_; lean_object* v_body_4598_; uint8_t v_binderInfo_4599_; lean_object* v___f_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_binderName_4596_ = lean_ctor_get(v_type_4586_, 0);
lean_inc(v_binderName_4596_);
v_binderType_4597_ = lean_ctor_get(v_type_4586_, 1);
lean_inc_ref(v_binderType_4597_);
v_body_4598_ = lean_ctor_get(v_type_4586_, 2);
lean_inc_ref(v_body_4598_);
v_binderInfo_4599_ = lean_ctor_get_uint8(v_type_4586_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_4586_);
lean_inc_ref(v_xs_4587_);
v___f_4600_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4600_, 0, v_xs_4587_);
lean_closure_set(v___f_4600_, 1, v_body_4598_);
v___x_4601_ = lean_expr_instantiate_rev(v_binderType_4597_, v_xs_4587_);
lean_dec_ref(v_xs_4587_);
lean_dec_ref(v_binderType_4597_);
v___x_4602_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4596_, v_binderInfo_4599_, v___x_4601_, v___f_4600_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
return v___x_4602_;
}
default: 
{
lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4603_ = lean_expr_instantiate_rev(v_type_4586_, v_xs_4587_);
lean_dec_ref(v_xs_4587_);
lean_dec_ref(v_type_4586_);
v___x_4604_ = l_Lean_Meta_whnfD(v___x_4603_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4620_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4620_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4620_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
switch(lean_obj_tag(v_a_4605_))
{
case 3:
{
lean_object* v_u_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
v_u_4609_ = lean_ctor_get(v_a_4605_, 0);
lean_inc(v_u_4609_);
lean_dec_ref(v_a_4605_);
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v_u_4609_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4610_);
v___x_4612_ = v___x_4607_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
case 7:
{
lean_object* v___x_4614_; 
lean_del_object(v___x_4607_);
v___x_4614_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4586_ = v_a_4605_;
v_xs_4587_ = v___x_4614_;
goto _start;
}
default: 
{
lean_object* v___x_4616_; lean_object* v___x_4618_; 
lean_dec(v_a_4605_);
v___x_4616_ = lean_box(0);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4616_);
v___x_4618_ = v___x_4607_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
v_a_4621_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4604_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4604_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4629_, lean_object* v_body_4630_, lean_object* v_x_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = lean_array_push(v_xs_4629_, v_x_4631_);
v___x_4638_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4630_, v___x_4637_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4639_, lean_object* v_xs_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4639_, v_xs_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4647_, lean_object* v_cache_4648_, lean_object* v_a_x3f_4649_){
_start:
{
lean_object* v___x_4651_; lean_object* v_mctx_4652_; lean_object* v_zetaDeltaFVarIds_4653_; lean_object* v_postponed_4654_; lean_object* v_diag_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4665_; 
v___x_4651_ = lean_st_ref_take(v_a_4647_);
v_mctx_4652_ = lean_ctor_get(v___x_4651_, 0);
v_zetaDeltaFVarIds_4653_ = lean_ctor_get(v___x_4651_, 2);
v_postponed_4654_ = lean_ctor_get(v___x_4651_, 3);
v_diag_4655_ = lean_ctor_get(v___x_4651_, 4);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4665_ == 0)
{
lean_object* v_unused_4666_; 
v_unused_4666_ = lean_ctor_get(v___x_4651_, 1);
lean_dec(v_unused_4666_);
v___x_4657_ = v___x_4651_;
v_isShared_4658_ = v_isSharedCheck_4665_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_diag_4655_);
lean_inc(v_postponed_4654_);
lean_inc(v_zetaDeltaFVarIds_4653_);
lean_inc(v_mctx_4652_);
lean_dec(v___x_4651_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4665_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 1, v_cache_4648_);
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_mctx_4652_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v_cache_4648_);
lean_ctor_set(v_reuseFailAlloc_4664_, 2, v_zetaDeltaFVarIds_4653_);
lean_ctor_set(v_reuseFailAlloc_4664_, 3, v_postponed_4654_);
lean_ctor_set(v_reuseFailAlloc_4664_, 4, v_diag_4655_);
v___x_4660_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = lean_st_ref_set(v_a_4647_, v___x_4660_);
v___x_4662_ = lean_box(0);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4667_, lean_object* v_cache_4668_, lean_object* v_a_x3f_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4667_, v_cache_4668_, v_a_x3f_4669_);
lean_dec(v_a_x3f_4669_);
lean_dec(v_a_4667_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4672_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v___x_4679_; lean_object* v_cache_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4679_ = lean_st_ref_get(v_a_4674_);
v_cache_4680_ = lean_ctor_get(v___x_4679_, 1);
lean_inc_ref(v_cache_4680_);
lean_dec(v___x_4679_);
v___x_4681_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4682_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4672_, v___x_4681_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4699_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4699_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4699_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
lean_inc(v_a_4683_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 1);
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
v___x_4689_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4674_, v_cache_4680_, v___x_4688_);
lean_dec_ref(v___x_4688_);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; 
v_unused_4697_ = lean_ctor_get(v___x_4689_, 0);
lean_dec(v_unused_4697_);
v___x_4691_ = v___x_4689_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_dec(v___x_4689_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v_a_4683_);
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4683_);
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
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
v_a_4700_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4700_);
lean_dec_ref(v___x_4682_);
v___x_4701_ = lean_box(0);
v___x_4702_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4674_, v_cache_4680_, v___x_4701_);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; 
v_unused_4710_ = lean_ctor_get(v___x_4702_, 0);
lean_dec(v_unused_4710_);
v___x_4704_ = v___x_4702_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_dec(v___x_4702_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set_tag(v___x_4704_, 1);
lean_ctor_set(v___x_4704_, 0, v_a_4700_);
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4700_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_object* v___x_4711_; 
lean_dec_ref(v_type_4672_);
v___x_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4678_);
return v___x_4711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_);
lean_dec(v_a_4716_);
lean_dec_ref(v_a_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4740_; 
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4728_ = v___x_4725_;
v_isShared_4729_ = v_isSharedCheck_4740_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4725_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4740_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
if (lean_obj_tag(v_a_4726_) == 0)
{
uint8_t v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4733_; 
v___x_4730_ = 0;
v___x_4731_ = lean_box(v___x_4730_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4731_);
v___x_4733_ = v___x_4728_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4731_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
else
{
uint8_t v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4738_; 
lean_dec_ref(v_a_4726_);
v___x_4735_ = 1;
v___x_4736_ = lean_box(v___x_4735_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4736_);
v___x_4738_ = v___x_4728_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
v_a_4741_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4725_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4725_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_Meta_isTypeFormerType(v_type_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
return v_res_4755_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_4756_, lean_object* v_x_4757_){
_start:
{
if (lean_obj_tag(v_x_4756_) == 0)
{
if (lean_obj_tag(v_x_4757_) == 0)
{
uint8_t v___x_4758_; 
v___x_4758_ = 1;
return v___x_4758_;
}
else
{
uint8_t v___x_4759_; 
v___x_4759_ = 0;
return v___x_4759_;
}
}
else
{
if (lean_obj_tag(v_x_4757_) == 0)
{
uint8_t v___x_4760_; 
v___x_4760_ = 0;
return v___x_4760_;
}
else
{
lean_object* v_val_4761_; lean_object* v_val_4762_; uint8_t v___x_4763_; 
v_val_4761_ = lean_ctor_get(v_x_4756_, 0);
v_val_4762_ = lean_ctor_get(v_x_4757_, 0);
v___x_4763_ = lean_level_eq(v_val_4761_, v_val_4762_);
return v___x_4763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_4764_, lean_object* v_x_4765_){
_start:
{
uint8_t v_res_4766_; lean_object* v_r_4767_; 
v_res_4766_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_4764_, v_x_4765_);
lean_dec(v_x_4765_);
lean_dec(v_x_4764_);
v_r_4767_ = lean_box(v_res_4766_);
return v_r_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4787_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4779_ = v___x_4776_;
v_isShared_4780_ = v_isSharedCheck_4787_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4787_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4781_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_4782_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_4777_, v___x_4781_);
lean_dec(v_a_4777_);
v___x_4783_ = lean_box(v___x_4782_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4783_);
v___x_4785_ = v___x_4779_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4795_; 
v_a_4788_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4790_ = v___x_4776_;
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4776_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4793_; 
if (v_isShared_4791_ == 0)
{
v___x_4793_ = v___x_4790_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4788_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Meta_isPropFormerType(v_type_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v___x_4809_; 
lean_inc(v_a_4807_);
lean_inc_ref(v_a_4806_);
lean_inc(v_a_4805_);
lean_inc_ref(v_a_4804_);
v___x_4809_ = lean_infer_type(v_e_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4811_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_a_4810_);
lean_dec_ref(v___x_4809_);
v___x_4811_ = l_Lean_Meta_isTypeFormerType(v_a_4810_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
return v___x_4811_;
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
v_a_4812_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4809_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4809_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Lean_Meta_isTypeFormer(v_e_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
lean_dec(v_a_4822_);
lean_dec_ref(v_a_4821_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_4827_, lean_object* v_maxFVars_x3f_4828_, lean_object* v_k_4829_, uint8_t v_cleanupAnnotations_4830_, uint8_t v_whnfType_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v___f_4837_; lean_object* v___x_4838_; 
v___f_4837_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4837_, 0, v_k_4829_);
v___x_4838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4827_, v_maxFVars_x3f_4828_, v___f_4837_, v_cleanupAnnotations_4830_, v_whnfType_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4838_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4838_);
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
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_a_4847_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4838_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4838_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_4855_, lean_object* v_maxFVars_x3f_4856_, lean_object* v_k_4857_, lean_object* v_cleanupAnnotations_4858_, lean_object* v_whnfType_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4865_; uint8_t v_whnfType_boxed_4866_; lean_object* v_res_4867_; 
v_cleanupAnnotations_boxed_4865_ = lean_unbox(v_cleanupAnnotations_4858_);
v_whnfType_boxed_4866_ = lean_unbox(v_whnfType_4859_);
v_res_4867_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4855_, v_maxFVars_x3f_4856_, v_k_4857_, v_cleanupAnnotations_boxed_4865_, v_whnfType_boxed_4866_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_4868_, lean_object* v_type_4869_, lean_object* v_maxFVars_x3f_4870_, lean_object* v_k_4871_, uint8_t v_cleanupAnnotations_4872_, uint8_t v_whnfType_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4869_, v_maxFVars_x3f_4870_, v_k_4871_, v_cleanupAnnotations_4872_, v_whnfType_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_4880_, lean_object* v_type_4881_, lean_object* v_maxFVars_x3f_4882_, lean_object* v_k_4883_, lean_object* v_cleanupAnnotations_4884_, lean_object* v_whnfType_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4891_; uint8_t v_whnfType_boxed_4892_; lean_object* v_res_4893_; 
v_cleanupAnnotations_boxed_4891_ = lean_unbox(v_cleanupAnnotations_4884_);
v_whnfType_boxed_4892_ = lean_unbox(v_whnfType_4885_);
v_res_4893_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_4880_, v_type_4881_, v_maxFVars_x3f_4882_, v_k_4883_, v_cleanupAnnotations_boxed_4891_, v_whnfType_boxed_4892_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
lean_dec(v___y_4889_);
lean_dec_ref(v___y_4888_);
lean_dec(v___y_4887_);
lean_dec_ref(v___y_4886_);
return v_res_4893_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_4894_, lean_object* v_as_4895_, size_t v_i_4896_, size_t v_stop_4897_){
_start:
{
uint8_t v___x_4898_; 
v___x_4898_ = lean_usize_dec_eq(v_i_4896_, v_stop_4897_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; uint8_t v___x_4900_; 
v___x_4899_ = lean_array_uget_borrowed(v_as_4895_, v_i_4896_);
v___x_4900_ = lean_expr_eqv(v_a_4894_, v___x_4899_);
if (v___x_4900_ == 0)
{
size_t v___x_4901_; size_t v___x_4902_; 
v___x_4901_ = ((size_t)1ULL);
v___x_4902_ = lean_usize_add(v_i_4896_, v___x_4901_);
v_i_4896_ = v___x_4902_;
goto _start;
}
else
{
return v___x_4900_;
}
}
else
{
uint8_t v___x_4904_; 
v___x_4904_ = 0;
return v___x_4904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_4905_, lean_object* v_as_4906_, lean_object* v_i_4907_, lean_object* v_stop_4908_){
_start:
{
size_t v_i_boxed_4909_; size_t v_stop_boxed_4910_; uint8_t v_res_4911_; lean_object* v_r_4912_; 
v_i_boxed_4909_ = lean_unbox_usize(v_i_4907_);
lean_dec(v_i_4907_);
v_stop_boxed_4910_ = lean_unbox_usize(v_stop_4908_);
lean_dec(v_stop_4908_);
v_res_4911_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4905_, v_as_4906_, v_i_boxed_4909_, v_stop_boxed_4910_);
lean_dec_ref(v_as_4906_);
lean_dec_ref(v_a_4905_);
v_r_4912_ = lean_box(v_res_4911_);
return v_r_4912_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; 
v___x_4915_ = lean_unsigned_to_nat(0u);
v___x_4916_ = lean_array_get_size(v_as_4913_);
v___x_4917_ = lean_nat_dec_lt(v___x_4915_, v___x_4916_);
if (v___x_4917_ == 0)
{
return v___x_4917_;
}
else
{
if (v___x_4917_ == 0)
{
return v___x_4917_;
}
else
{
size_t v___x_4918_; size_t v___x_4919_; uint8_t v___x_4920_; 
v___x_4918_ = ((size_t)0ULL);
v___x_4919_ = lean_usize_of_nat(v___x_4916_);
v___x_4920_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4914_, v_as_4913_, v___x_4918_, v___x_4919_);
return v___x_4920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_4921_, lean_object* v_a_4922_){
_start:
{
uint8_t v_res_4923_; lean_object* v_r_4924_; 
v_res_4923_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_4921_, v_a_4922_);
lean_dec_ref(v_a_4922_);
lean_dec_ref(v_as_4921_);
v_r_4924_ = lean_box(v_res_4923_);
return v_r_4924_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_4925_, lean_object* v_e_4926_){
_start:
{
uint8_t v___x_4927_; lean_object* v_d_4929_; lean_object* v_b_4930_; 
v___x_4927_ = l_Lean_Expr_hasFVar(v_e_4926_);
if (v___x_4927_ == 0)
{
lean_dec_ref(v_e_4926_);
return v___x_4927_;
}
else
{
switch(lean_obj_tag(v_e_4926_))
{
case 7:
{
lean_object* v_binderType_4933_; lean_object* v_body_4934_; 
v_binderType_4933_ = lean_ctor_get(v_e_4926_, 1);
lean_inc_ref(v_binderType_4933_);
v_body_4934_ = lean_ctor_get(v_e_4926_, 2);
lean_inc_ref(v_body_4934_);
lean_dec_ref(v_e_4926_);
v_d_4929_ = v_binderType_4933_;
v_b_4930_ = v_body_4934_;
goto v___jp_4928_;
}
case 6:
{
lean_object* v_binderType_4935_; lean_object* v_body_4936_; 
v_binderType_4935_ = lean_ctor_get(v_e_4926_, 1);
lean_inc_ref(v_binderType_4935_);
v_body_4936_ = lean_ctor_get(v_e_4926_, 2);
lean_inc_ref(v_body_4936_);
lean_dec_ref(v_e_4926_);
v_d_4929_ = v_binderType_4935_;
v_b_4930_ = v_body_4936_;
goto v___jp_4928_;
}
case 10:
{
lean_object* v_expr_4937_; 
v_expr_4937_ = lean_ctor_get(v_e_4926_, 1);
lean_inc_ref(v_expr_4937_);
lean_dec_ref(v_e_4926_);
v_e_4926_ = v_expr_4937_;
goto _start;
}
case 8:
{
lean_object* v_type_4939_; lean_object* v_value_4940_; lean_object* v_body_4941_; uint8_t v___x_4942_; 
v_type_4939_ = lean_ctor_get(v_e_4926_, 1);
lean_inc_ref(v_type_4939_);
v_value_4940_ = lean_ctor_get(v_e_4926_, 2);
lean_inc_ref(v_value_4940_);
v_body_4941_ = lean_ctor_get(v_e_4926_, 3);
lean_inc_ref(v_body_4941_);
lean_dec_ref(v_e_4926_);
v___x_4942_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4925_, v_type_4939_);
if (v___x_4942_ == 0)
{
uint8_t v___x_4943_; 
v___x_4943_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4925_, v_value_4940_);
if (v___x_4943_ == 0)
{
v_e_4926_ = v_body_4941_;
goto _start;
}
else
{
lean_dec_ref(v_body_4941_);
return v___x_4927_;
}
}
else
{
lean_dec_ref(v_body_4941_);
lean_dec_ref(v_value_4940_);
return v___x_4927_;
}
}
case 5:
{
lean_object* v_fn_4945_; lean_object* v_arg_4946_; uint8_t v___x_4947_; 
v_fn_4945_ = lean_ctor_get(v_e_4926_, 0);
lean_inc_ref(v_fn_4945_);
v_arg_4946_ = lean_ctor_get(v_e_4926_, 1);
lean_inc_ref(v_arg_4946_);
lean_dec_ref(v_e_4926_);
v___x_4947_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4925_, v_fn_4945_);
if (v___x_4947_ == 0)
{
v_e_4926_ = v_arg_4946_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4946_);
return v___x_4927_;
}
}
case 11:
{
lean_object* v_struct_4949_; 
v_struct_4949_ = lean_ctor_get(v_e_4926_, 2);
lean_inc_ref(v_struct_4949_);
lean_dec_ref(v_e_4926_);
v_e_4926_ = v_struct_4949_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4951_; lean_object* v___x_4952_; uint8_t v___x_4953_; 
v_fvarId_4951_ = lean_ctor_get(v_e_4926_, 0);
lean_inc(v_fvarId_4951_);
lean_dec_ref(v_e_4926_);
v___x_4952_ = l_Lean_Expr_fvar___override(v_fvarId_4951_);
v___x_4953_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_4925_, v___x_4952_);
lean_dec_ref(v___x_4952_);
return v___x_4953_;
}
default: 
{
uint8_t v___x_4954_; 
lean_dec_ref(v_e_4926_);
v___x_4954_ = 0;
return v___x_4954_;
}
}
}
v___jp_4928_:
{
uint8_t v___x_4931_; 
v___x_4931_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4925_, v_d_4929_);
if (v___x_4931_ == 0)
{
v_e_4926_ = v_b_4930_;
goto _start;
}
else
{
lean_dec_ref(v_b_4930_);
return v___x_4927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_4955_, lean_object* v_e_4956_){
_start:
{
uint8_t v_res_4957_; lean_object* v_r_4958_; 
v_res_4957_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4955_, v_e_4956_);
lean_dec_ref(v_xs_4955_);
v_r_4958_ = lean_box(v_res_4957_);
return v_r_4958_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
return v___x_4961_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_4964_ = l_Lean_stringToMessageData(v___x_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_4965_, lean_object* v_type_4966_, lean_object* v_as_4967_, size_t v_sz_4968_, size_t v_i_4969_, lean_object* v_b_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v_a_4977_; uint8_t v___x_4981_; 
v___x_4981_ = lean_usize_dec_lt(v_i_4969_, v_sz_4968_);
if (v___x_4981_ == 0)
{
lean_object* v___x_4982_; 
lean_dec_ref(v_type_4966_);
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v_b_4970_);
return v___x_4982_;
}
else
{
lean_object* v___x_4983_; lean_object* v_a_4984_; uint8_t v___x_4985_; 
v___x_4983_ = lean_box(0);
v_a_4984_ = lean_array_uget_borrowed(v_as_4967_, v_i_4969_);
lean_inc(v_a_4984_);
v___x_4985_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4965_, v_a_4984_);
if (v___x_4985_ == 0)
{
v_a_4977_ = v___x_4983_;
goto v___jp_4976_;
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4986_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_4984_);
v___x_4987_ = l_Lean_MessageData_ofExpr(v_a_4984_);
v___x_4988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4986_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
v___x_4989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
lean_inc_ref(v_type_4966_);
v___x_4991_ = l_Lean_MessageData_ofExpr(v_type_4966_);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_4992_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_dec_ref(v___x_4993_);
v_a_4977_ = v___x_4983_;
goto v___jp_4976_;
}
else
{
lean_dec_ref(v_type_4966_);
return v___x_4993_;
}
}
}
v___jp_4976_:
{
size_t v___x_4978_; size_t v___x_4979_; 
v___x_4978_ = ((size_t)1ULL);
v___x_4979_ = lean_usize_add(v_i_4969_, v___x_4978_);
v_i_4969_ = v___x_4979_;
v_b_4970_ = v_a_4977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_4994_, lean_object* v_type_4995_, lean_object* v_as_4996_, lean_object* v_sz_4997_, lean_object* v_i_4998_, lean_object* v_b_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
size_t v_sz_boxed_5005_; size_t v_i_boxed_5006_; lean_object* v_res_5007_; 
v_sz_boxed_5005_ = lean_unbox_usize(v_sz_4997_);
lean_dec(v_sz_4997_);
v_i_boxed_5006_ = lean_unbox_usize(v_i_4998_);
lean_dec(v_i_4998_);
v_res_5007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_4994_, v_type_4995_, v_as_4996_, v_sz_boxed_5005_, v_i_boxed_5006_, v_b_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec_ref(v_as_4996_);
lean_dec_ref(v_xs_4994_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5008_, size_t v_i_5009_, lean_object* v_bs_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
uint8_t v___x_5016_; 
v___x_5016_ = lean_usize_dec_lt(v_i_5009_, v_sz_5008_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; 
v___x_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5017_, 0, v_bs_5010_);
return v___x_5017_;
}
else
{
lean_object* v_v_5018_; lean_object* v___x_5019_; 
v_v_5018_ = lean_array_uget_borrowed(v_bs_5010_, v_i_5009_);
lean_inc(v___y_5014_);
lean_inc_ref(v___y_5013_);
lean_inc(v___y_5012_);
lean_inc_ref(v___y_5011_);
lean_inc(v_v_5018_);
v___x_5019_ = lean_infer_type(v_v_5018_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v___x_5021_; lean_object* v_bs_x27_5022_; size_t v___x_5023_; size_t v___x_5024_; lean_object* v___x_5025_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
lean_dec_ref(v___x_5019_);
v___x_5021_ = lean_unsigned_to_nat(0u);
v_bs_x27_5022_ = lean_array_uset(v_bs_5010_, v_i_5009_, v___x_5021_);
v___x_5023_ = ((size_t)1ULL);
v___x_5024_ = lean_usize_add(v_i_5009_, v___x_5023_);
v___x_5025_ = lean_array_uset(v_bs_x27_5022_, v_i_5009_, v_a_5020_);
v_i_5009_ = v___x_5024_;
v_bs_5010_ = v___x_5025_;
goto _start;
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5034_; 
lean_dec_ref(v_bs_5010_);
v_a_5027_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5029_ = v___x_5019_;
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5019_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5032_; 
if (v_isShared_5030_ == 0)
{
v___x_5032_ = v___x_5029_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_a_5027_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5035_, lean_object* v_i_5036_, lean_object* v_bs_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
size_t v_sz_boxed_5043_; size_t v_i_boxed_5044_; lean_object* v_res_5045_; 
v_sz_boxed_5043_ = lean_unbox_usize(v_sz_5035_);
lean_dec(v_sz_5035_);
v_i_boxed_5044_ = lean_unbox_usize(v_i_5036_);
lean_dec(v_i_5036_);
v_res_5045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5043_, v_i_boxed_5044_, v_bs_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
return v_res_5045_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5048_ = l_Lean_stringToMessageData(v___x_5047_);
return v___x_5048_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5051_ = l_Lean_stringToMessageData(v___x_5050_);
return v___x_5051_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5054_ = l_Lean_stringToMessageData(v___x_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5055_, lean_object* v_n_5056_, lean_object* v_xs_5057_, lean_object* v_x_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
lean_object* v___x_5088_; uint8_t v___x_5089_; 
v___x_5088_ = lean_array_get_size(v_xs_5057_);
v___x_5089_ = lean_nat_dec_eq(v___x_5088_, v_n_5056_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5109_; 
lean_dec_ref(v_xs_5057_);
v___x_5090_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5091_ = l_Lean_MessageData_ofExpr(v_type_5055_);
v___x_5092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5090_);
lean_ctor_set(v___x_5092_, 1, v___x_5091_);
v___x_5093_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5094_, 0, v___x_5092_);
lean_ctor_set(v___x_5094_, 1, v___x_5093_);
v___x_5095_ = l_Nat_reprFast(v_n_5056_);
v___x_5096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5095_);
v___x_5097_ = l_Lean_MessageData_ofFormat(v___x_5096_);
v___x_5098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5098_, 0, v___x_5094_);
lean_ctor_set(v___x_5098_, 1, v___x_5097_);
v___x_5099_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5098_);
lean_ctor_set(v___x_5100_, 1, v___x_5099_);
v___x_5101_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5100_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5104_ = v___x_5101_;
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5101_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5105_ == 0)
{
v___x_5107_ = v___x_5104_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_a_5102_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
else
{
lean_dec(v_n_5056_);
goto v___jp_5064_;
}
v___jp_5064_:
{
size_t v_sz_5065_; size_t v___x_5066_; lean_object* v___x_5067_; 
v_sz_5065_ = lean_array_size(v_xs_5057_);
v___x_5066_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5057_);
v___x_5067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5065_, v___x_5066_, v_xs_5057_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5069_; size_t v_sz_5070_; lean_object* v___x_5071_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_a_5068_);
lean_dec_ref(v___x_5067_);
v___x_5069_ = lean_box(0);
v_sz_5070_ = lean_array_size(v_a_5068_);
v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5057_, v_type_5055_, v_a_5068_, v_sz_5070_, v___x_5066_, v___x_5069_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
lean_dec_ref(v_xs_5057_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5078_ == 0)
{
lean_object* v_unused_5079_; 
v_unused_5079_ = lean_ctor_get(v___x_5071_, 0);
lean_dec(v_unused_5079_);
v___x_5073_ = v___x_5071_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_dec(v___x_5071_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v_a_5068_);
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5068_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_dec(v_a_5068_);
v_a_5080_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_5071_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5071_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5057_);
lean_dec_ref(v_type_5055_);
return v___x_5067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5110_, lean_object* v_n_5111_, lean_object* v_xs_5112_, lean_object* v_x_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5110_, v_n_5111_, v_xs_5112_, v_x_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec_ref(v_x_5113_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5120_, lean_object* v_type_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_){
_start:
{
lean_object* v___f_5127_; lean_object* v___x_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; 
lean_inc(v_n_5120_);
lean_inc_ref(v_type_5121_);
v___f_5127_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5127_, 0, v_type_5121_);
lean_closure_set(v___f_5127_, 1, v_n_5120_);
v___x_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5128_, 0, v_n_5120_);
v___x_5129_ = 0;
v___x_5130_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5121_, v___x_5128_, v___f_5127_, v___x_5129_, v___x_5129_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5131_, lean_object* v_type_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Lean_Meta_arrowDomainsN(v_n_5131_, v_type_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_);
lean_dec(v_a_5136_);
lean_dec_ref(v_a_5135_);
lean_dec(v_a_5134_);
lean_dec_ref(v_a_5133_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5139_, lean_object* v_e_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_){
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
lean_dec_ref(v___x_5146_);
v___x_5148_ = l_Lean_Meta_arrowDomainsN(v_n_5139_, v_a_5147_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_);
return v___x_5148_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec(v_n_5139_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5157_, lean_object* v_e_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lean_Meta_inferArgumentTypesN(v_n_5157_, v_e_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_a_5162_);
lean_dec_ref(v_a_5161_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
return v_res_5164_;
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
