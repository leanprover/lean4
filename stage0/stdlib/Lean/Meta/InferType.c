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
v___x_889_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
lean_ctor_set(v___x_889_, 3, v___x_887_);
lean_ctor_set(v___x_889_, 4, v___x_887_);
lean_ctor_set(v___x_889_, 5, v___x_887_);
lean_ctor_set(v___x_889_, 6, v___x_887_);
lean_ctor_set(v___x_889_, 7, v___x_887_);
lean_ctor_set(v___x_889_, 8, v___x_887_);
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
size_t v_x_1240__boxed_1758_; size_t v_x_1241__boxed_1759_; lean_object* v_res_1760_; 
v_x_1240__boxed_1758_ = lean_unbox_usize(v_x_1754_);
lean_dec(v_x_1754_);
v_x_1241__boxed_1759_ = lean_unbox_usize(v_x_1755_);
lean_dec(v_x_1755_);
v_res_1760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1753_, v_x_1240__boxed_1758_, v_x_1241__boxed_1759_, v_x_1756_, v_x_1757_);
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
lean_object* v___x_1772_; lean_object* v_mctx_1773_; lean_object* v_cache_1774_; lean_object* v_zetaDeltaFVarIds_1775_; lean_object* v_postponed_1776_; lean_object* v_diag_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1804_; 
v___x_1772_ = lean_st_ref_take(v___y_1770_);
v_mctx_1773_ = lean_ctor_get(v___x_1772_, 0);
v_cache_1774_ = lean_ctor_get(v___x_1772_, 1);
v_zetaDeltaFVarIds_1775_ = lean_ctor_get(v___x_1772_, 2);
v_postponed_1776_ = lean_ctor_get(v___x_1772_, 3);
v_diag_1777_ = lean_ctor_get(v___x_1772_, 4);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1779_ = v___x_1772_;
v_isShared_1780_ = v_isSharedCheck_1804_;
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
v_isShared_1780_ = v_isSharedCheck_1804_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_depth_1781_; lean_object* v_levelAssignDepth_1782_; lean_object* v_mvarCounter_1783_; lean_object* v_lDepth_1784_; lean_object* v_decls_1785_; lean_object* v_userNames_1786_; lean_object* v_lAssignment_1787_; lean_object* v_eAssignment_1788_; lean_object* v_dAssignment_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1803_; 
v_depth_1781_ = lean_ctor_get(v_mctx_1773_, 0);
v_levelAssignDepth_1782_ = lean_ctor_get(v_mctx_1773_, 1);
v_mvarCounter_1783_ = lean_ctor_get(v_mctx_1773_, 2);
v_lDepth_1784_ = lean_ctor_get(v_mctx_1773_, 3);
v_decls_1785_ = lean_ctor_get(v_mctx_1773_, 4);
v_userNames_1786_ = lean_ctor_get(v_mctx_1773_, 5);
v_lAssignment_1787_ = lean_ctor_get(v_mctx_1773_, 6);
v_eAssignment_1788_ = lean_ctor_get(v_mctx_1773_, 7);
v_dAssignment_1789_ = lean_ctor_get(v_mctx_1773_, 8);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_mctx_1773_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1791_ = v_mctx_1773_;
v_isShared_1792_ = v_isSharedCheck_1803_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_dAssignment_1789_);
lean_inc(v_eAssignment_1788_);
lean_inc(v_lAssignment_1787_);
lean_inc(v_userNames_1786_);
lean_inc(v_decls_1785_);
lean_inc(v_lDepth_1784_);
lean_inc(v_mvarCounter_1783_);
lean_inc(v_levelAssignDepth_1782_);
lean_inc(v_depth_1781_);
lean_dec(v_mctx_1773_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1803_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1788_, v_mvarId_1768_, v_val_1769_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 7, v___x_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_depth_1781_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_levelAssignDepth_1782_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_mvarCounter_1783_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_lDepth_1784_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_decls_1785_);
lean_ctor_set(v_reuseFailAlloc_1802_, 5, v_userNames_1786_);
lean_ctor_set(v_reuseFailAlloc_1802_, 6, v_lAssignment_1787_);
lean_ctor_set(v_reuseFailAlloc_1802_, 7, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1802_, 8, v_dAssignment_1789_);
v___x_1795_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1795_);
v___x_1797_ = v___x_1779_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_cache_1774_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_zetaDeltaFVarIds_1775_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_postponed_1776_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_diag_1777_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_st_ref_set(v___y_1770_, v___x_1797_);
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1805_, lean_object* v_val_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1805_, v_val_1806_, v___y_1807_);
lean_dec(v___y_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1816_; 
lean_inc(v_a_1814_);
lean_inc_ref(v_a_1813_);
lean_inc(v_a_1812_);
lean_inc_ref(v_a_1811_);
lean_inc_ref(v_type_1810_);
v___x_1816_ = lean_infer_type(v_type_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = l_Lean_Meta_whnfD(v_a_1817_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1853_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1853_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1853_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
switch(lean_obj_tag(v_a_1819_))
{
case 3:
{
lean_object* v_u_1823_; lean_object* v___x_1825_; 
lean_dec_ref(v_type_1810_);
v_u_1823_ = lean_ctor_get(v_a_1819_, 0);
lean_inc(v_u_1823_);
lean_dec_ref(v_a_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v_u_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_u_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
case 2:
{
lean_object* v_mvarId_1827_; lean_object* v___x_1828_; 
lean_del_object(v___x_1821_);
v_mvarId_1827_ = lean_ctor_get(v_a_1819_, 0);
lean_inc_n(v_mvarId_1827_, 2);
lean_dec_ref(v_a_1819_);
v___x_1828_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1827_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; uint8_t v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = lean_unbox(v_a_1829_);
lean_dec(v_a_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec_ref(v_type_1810_);
v___x_1831_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc_n(v_a_1832_, 2);
lean_dec_ref(v___x_1831_);
v___x_1833_ = l_Lean_mkSort(v_a_1832_);
v___x_1834_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1827_, v___x_1833_, v_a_1812_);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v___x_1834_, 0);
lean_dec(v_unused_1842_);
v___x_1836_ = v___x_1834_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v___x_1834_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v_a_1832_);
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1832_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_dec(v_mvarId_1827_);
return v___x_1831_;
}
}
else
{
lean_object* v___x_1843_; 
lean_dec(v_mvarId_1827_);
v___x_1843_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
return v___x_1843_;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_mvarId_1827_);
lean_dec_ref(v_type_1810_);
v_a_1844_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1828_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1828_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
default: 
{
lean_object* v___x_1852_; 
lean_del_object(v___x_1821_);
lean_dec(v_a_1819_);
v___x_1852_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_type_1810_);
v_a_1854_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1818_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1818_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_type_1810_);
v_a_1862_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1816_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1816_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_getLevel(v_type_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1877_, lean_object* v_val_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1877_, v_val_1878_, v___y_1880_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1885_, lean_object* v_val_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1885_, v_val_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1894_, v_x_1895_, v_x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1898_, lean_object* v_x_1899_, size_t v_x_1900_, size_t v_x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1899_, v_x_1900_, v_x_1901_, v_x_1902_, v_x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_){
_start:
{
size_t v_x_1599__boxed_1911_; size_t v_x_1600__boxed_1912_; lean_object* v_res_1913_; 
v_x_1599__boxed_1911_ = lean_unbox_usize(v_x_1907_);
lean_dec(v_x_1907_);
v_x_1600__boxed_1912_ = lean_unbox_usize(v_x_1908_);
lean_dec(v_x_1908_);
v_res_1913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1905_, v_x_1906_, v_x_1599__boxed_1911_, v_x_1600__boxed_1912_, v_x_1909_, v_x_1910_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1914_, lean_object* v_n_1915_, lean_object* v_k_1916_, lean_object* v_v_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1915_, v_k_1916_, v_v_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1919_, size_t v_depth_1920_, lean_object* v_keys_1921_, lean_object* v_vals_1922_, lean_object* v_heq_1923_, lean_object* v_i_1924_, lean_object* v_entries_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1920_, v_keys_1921_, v_vals_1922_, v_i_1924_, v_entries_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1927_, lean_object* v_depth_1928_, lean_object* v_keys_1929_, lean_object* v_vals_1930_, lean_object* v_heq_1931_, lean_object* v_i_1932_, lean_object* v_entries_1933_){
_start:
{
size_t v_depth_boxed_1934_; lean_object* v_res_1935_; 
v_depth_boxed_1934_ = lean_unbox_usize(v_depth_1928_);
lean_dec(v_depth_1928_);
v_res_1935_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1927_, v_depth_boxed_1934_, v_keys_1929_, v_vals_1930_, v_heq_1931_, v_i_1932_, v_entries_1933_);
lean_dec_ref(v_vals_1930_);
lean_dec_ref(v_keys_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1936_, lean_object* v_x_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1937_, v_x_1938_, v_x_1939_, v_x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_1942_, lean_object* v_b_1943_, lean_object* v_c_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v___x_1950_ = lean_apply_7(v_k_1942_, v_b_1943_, v_c_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_1951_, lean_object* v_b_1952_, lean_object* v_c_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_1951_, v_b_1952_, v_c_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_1960_, lean_object* v_k_1961_, uint8_t v_cleanupAnnotations_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___f_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1968_, 0, v_k_1961_);
v___x_1969_ = 0;
v___x_1970_ = lean_box(0);
v___x_1971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1969_, v___x_1970_, v_type_1960_, v___f_1968_, v_cleanupAnnotations_1962_, v___x_1969_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_1988_, lean_object* v_k_1989_, lean_object* v_cleanupAnnotations_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1996_; lean_object* v_res_1997_; 
v_cleanupAnnotations_boxed_1996_ = lean_unbox(v_cleanupAnnotations_1990_);
v_res_1997_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_1988_, v_k_1989_, v_cleanupAnnotations_boxed_1996_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_1998_, lean_object* v_type_1999_, lean_object* v_k_2000_, uint8_t v_cleanupAnnotations_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_1999_, v_k_2000_, v_cleanupAnnotations_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2008_, lean_object* v_type_2009_, lean_object* v_k_2010_, lean_object* v_cleanupAnnotations_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2017_; lean_object* v_res_2018_; 
v_cleanupAnnotations_boxed_2017_ = lean_unbox(v_cleanupAnnotations_2011_);
v_res_2018_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2008_, v_type_2009_, v_k_2010_, v_cleanupAnnotations_boxed_2017_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2019_, size_t v_i_2020_, size_t v_stop_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_usize_dec_eq(v_i_2020_, v_stop_2021_);
if (v___x_2028_ == 0)
{
size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_sub(v_i_2020_, v___x_2029_);
v___x_2031_ = lean_array_uget_borrowed(v_as_2019_, v___x_2030_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___x_2031_);
v___x_2032_ = lean_infer_type(v___x_2031_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = l_Lean_Meta_getLevel(v_a_2033_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = l_Lean_mkLevelIMax_x27(v_a_2035_, v_b_2022_);
v_i_2020_ = v___x_2030_;
v_b_2022_ = v___x_2036_;
goto _start;
}
else
{
lean_dec(v_b_2022_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2034_);
v_i_2020_ = v___x_2030_;
v_b_2022_ = v_a_2038_;
goto _start;
}
else
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_b_2022_);
v_a_2040_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2032_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2032_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2022_);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2049_, lean_object* v_i_2050_, lean_object* v_stop_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
size_t v_i_boxed_2058_; size_t v_stop_boxed_2059_; lean_object* v_res_2060_; 
v_i_boxed_2058_ = lean_unbox_usize(v_i_2050_);
lean_dec(v_i_2050_);
v_stop_boxed_2059_ = lean_unbox_usize(v_stop_2051_);
lean_dec(v_stop_2051_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2049_, v_i_boxed_2058_, v_stop_boxed_2059_, v_b_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_as_2049_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2061_, lean_object* v_e_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___y_2069_; lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_getLevel(v_e_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
v___x_2090_ = lean_array_get_size(v_xs_2061_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_nat_dec_lt(v___x_2091_, v___x_2090_);
if (v___x_2092_ == 0)
{
lean_dec(v_a_2089_);
v___y_2069_ = v___x_2088_;
goto v___jp_2068_;
}
else
{
size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v___x_2088_);
v___x_2093_ = lean_usize_of_nat(v___x_2090_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2061_, v___x_2093_, v___x_2094_, v_a_2089_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v___y_2069_ = v___x_2095_;
goto v___jp_2068_;
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_a_2096_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2088_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2088_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
v___jp_2068_:
{
if (lean_obj_tag(v___y_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2079_; 
v_a_2070_ = lean_ctor_get(v___y_2069_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___y_2069_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2072_ = v___y_2069_;
v_isShared_2073_ = v_isSharedCheck_2079_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___y_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2079_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2074_ = l_Lean_Level_normalize(v_a_2070_);
lean_dec(v_a_2070_);
v___x_2075_ = l_Lean_mkSort(v___x_2074_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2075_);
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
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
v_a_2080_ = lean_ctor_get(v___y_2069_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___y_2069_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___y_2069_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___y_2069_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2104_, lean_object* v_e_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2104_, v_e_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec_ref(v_xs_2104_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___f_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___f_2119_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2120_ = 0;
v___x_2121_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2113_, v___f_2119_, v___x_2120_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2129_, lean_object* v_k_2130_, uint8_t v_cleanupAnnotations_2131_, uint8_t v_preserveNondepLet_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___f_2138_; uint8_t v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___f_2138_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2138_, 0, v_k_2130_);
v___x_2139_ = 1;
v___x_2140_ = 0;
v___x_2141_ = lean_box(0);
v___x_2142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2129_, v___x_2139_, v___x_2139_, v_preserveNondepLet_2132_, v___x_2140_, v___x_2141_, v___f_2138_, v_cleanupAnnotations_2131_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_a_2151_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2142_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2142_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2159_, lean_object* v_k_2160_, lean_object* v_cleanupAnnotations_2161_, lean_object* v_preserveNondepLet_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2168_; uint8_t v_preserveNondepLet_boxed_2169_; lean_object* v_res_2170_; 
v_cleanupAnnotations_boxed_2168_ = lean_unbox(v_cleanupAnnotations_2161_);
v_preserveNondepLet_boxed_2169_ = lean_unbox(v_preserveNondepLet_2162_);
v_res_2170_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2159_, v_k_2160_, v_cleanupAnnotations_boxed_2168_, v_preserveNondepLet_boxed_2169_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2171_, lean_object* v_e_2172_, lean_object* v_k_2173_, uint8_t v_cleanupAnnotations_2174_, uint8_t v_preserveNondepLet_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2172_, v_k_2173_, v_cleanupAnnotations_2174_, v_preserveNondepLet_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2182_, lean_object* v_e_2183_, lean_object* v_k_2184_, lean_object* v_cleanupAnnotations_2185_, lean_object* v_preserveNondepLet_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2192_; uint8_t v_preserveNondepLet_boxed_2193_; lean_object* v_res_2194_; 
v_cleanupAnnotations_boxed_2192_ = lean_unbox(v_cleanupAnnotations_2185_);
v_preserveNondepLet_boxed_2193_ = lean_unbox(v_preserveNondepLet_2186_);
v_res_2194_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2182_, v_e_2183_, v_k_2184_, v_cleanupAnnotations_boxed_2192_, v_preserveNondepLet_boxed_2193_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2195_, lean_object* v_e_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2202_; 
lean_inc(v___y_2200_);
lean_inc_ref(v___y_2199_);
lean_inc(v___y_2198_);
lean_inc_ref(v___y_2197_);
v___x_2202_ = lean_infer_type(v_e_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; uint8_t v___x_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = 0;
v___x_2205_ = 1;
v___x_2206_ = 1;
v___x_2207_ = l_Lean_Meta_mkForallFVars(v_xs_2195_, v_a_2203_, v___x_2204_, v___x_2205_, v___x_2204_, v___x_2206_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
return v___x_2207_;
}
else
{
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2208_, lean_object* v_e_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2208_, v_e_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec_ref(v_xs_2208_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___f_2223_; uint8_t v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; 
v___f_2223_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2224_ = 0;
v___x_2225_ = 1;
v___x_2226_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2217_, v___f_2223_, v___x_2224_, v___x_2225_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
return v_res_2233_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2246_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2247_ = l_Lean_MessageData_ofName(v_mvarId_2240_);
v___x_2248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2250_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2259_, lean_object* v_mvarId_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2267_, lean_object* v_mvarId_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2267_, v_mvarId_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v_mctx_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_st_ref_get(v_a_2277_);
v_mctx_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc_ref(v_mctx_2282_);
lean_dec(v___x_2281_);
v___x_2283_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2282_, v_mvarId_2275_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2284_;
}
else
{
lean_object* v_val_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_mvarId_2275_);
v_val_2285_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_val_2285_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_type_2289_; lean_object* v___x_2291_; 
v_type_2289_ = lean_ctor_get(v_val_2285_, 2);
lean_inc_ref(v_type_2289_);
lean_dec(v_val_2285_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set_tag(v___x_2287_, 0);
lean_ctor_set(v___x_2287_, 0, v_type_2289_);
v___x_2291_ = v___x_2287_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_type_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_lctx_2306_; lean_object* v___x_2307_; 
v_lctx_2306_ = lean_ctor_get(v_a_2302_, 2);
lean_inc(v_fvarId_2301_);
lean_inc_ref(v_lctx_2306_);
v___x_2307_ = lean_local_ctx_find(v_lctx_2306_, v_fvarId_2301_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2301_, v_a_2303_, v_a_2304_);
return v___x_2308_;
}
else
{
lean_object* v_val_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_fvarId_2301_);
v_val_2309_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2311_ = v___x_2307_;
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_val_2309_);
lean_dec(v___x_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = l_Lean_LocalDecl_type(v_val_2309_);
lean_dec(v_val_2309_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set_tag(v___x_2311_, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2313_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_a_2319_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2324_, v_a_2325_, v_a_2327_, v_a_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2340_, lean_object* v_inferType_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
uint8_t v_cacheInferType_2347_; 
v_cacheInferType_2347_ = lean_ctor_get_uint8(v_a_2342_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref(v_e_2340_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
v___x_2348_ = lean_apply_5(v_inferType_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, lean_box(0));
return v___x_2348_;
}
else
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Lean_Expr_hasMVar(v_e_2340_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2340_, v_a_2342_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2404_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2404_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2404_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v_cache_2356_; lean_object* v_inferType_2357_; lean_object* v___f_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2355_ = lean_st_ref_get(v_a_2343_);
v_cache_2356_ = lean_ctor_get(v___x_2355_, 1);
lean_inc_ref(v_cache_2356_);
lean_dec(v___x_2355_);
v_inferType_2357_ = lean_ctor_get(v_cache_2356_, 0);
lean_inc_ref(v_inferType_2357_);
lean_dec_ref(v_cache_2356_);
v___f_2358_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0));
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1));
lean_inc(v_a_2351_);
v___x_2360_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2358_, v___x_2359_, v_inferType_2357_, v_a_2351_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; 
lean_del_object(v___x_2353_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
v___x_2361_ = lean_apply_5(v_inferType_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, lean_box(0));
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; uint8_t v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
v___x_2363_ = l_Lean_Expr_hasMVar(v_a_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2398_; 
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2361_, 0);
lean_dec(v_unused_2399_);
v___x_2365_ = v___x_2361_;
v_isShared_2366_ = v_isSharedCheck_2398_;
goto v_resetjp_2364_;
}
else
{
lean_dec(v___x_2361_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2398_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v_cache_2368_; lean_object* v_mctx_2369_; lean_object* v_zetaDeltaFVarIds_2370_; lean_object* v_postponed_2371_; lean_object* v_diag_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2397_; 
v___x_2367_ = lean_st_ref_take(v_a_2343_);
v_cache_2368_ = lean_ctor_get(v___x_2367_, 1);
v_mctx_2369_ = lean_ctor_get(v___x_2367_, 0);
v_zetaDeltaFVarIds_2370_ = lean_ctor_get(v___x_2367_, 2);
v_postponed_2371_ = lean_ctor_get(v___x_2367_, 3);
v_diag_2372_ = lean_ctor_get(v___x_2367_, 4);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2374_ = v___x_2367_;
v_isShared_2375_ = v_isSharedCheck_2397_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_diag_2372_);
lean_inc(v_postponed_2371_);
lean_inc(v_zetaDeltaFVarIds_2370_);
lean_inc(v_cache_2368_);
lean_inc(v_mctx_2369_);
lean_dec(v___x_2367_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2397_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_inferType_2376_; lean_object* v_funInfo_2377_; lean_object* v_synthInstance_2378_; lean_object* v_whnf_2379_; lean_object* v_defEqTrans_2380_; lean_object* v_defEqPerm_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2396_; 
v_inferType_2376_ = lean_ctor_get(v_cache_2368_, 0);
v_funInfo_2377_ = lean_ctor_get(v_cache_2368_, 1);
v_synthInstance_2378_ = lean_ctor_get(v_cache_2368_, 2);
v_whnf_2379_ = lean_ctor_get(v_cache_2368_, 3);
v_defEqTrans_2380_ = lean_ctor_get(v_cache_2368_, 4);
v_defEqPerm_2381_ = lean_ctor_get(v_cache_2368_, 5);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_cache_2368_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2383_ = v_cache_2368_;
v_isShared_2384_ = v_isSharedCheck_2396_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_defEqPerm_2381_);
lean_inc(v_defEqTrans_2380_);
lean_inc(v_whnf_2379_);
lean_inc(v_synthInstance_2378_);
lean_inc(v_funInfo_2377_);
lean_inc(v_inferType_2376_);
lean_dec(v_cache_2368_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2396_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_inc(v_a_2362_);
v___x_2385_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2358_, v___x_2359_, v_inferType_2376_, v_a_2351_, v_a_2362_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_funInfo_2377_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_synthInstance_2378_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_whnf_2379_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_defEqTrans_2380_);
lean_ctor_set(v_reuseFailAlloc_2395_, 5, v_defEqPerm_2381_);
v___x_2387_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 1, v___x_2387_);
v___x_2389_ = v___x_2374_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_mctx_2369_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_zetaDeltaFVarIds_2370_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_postponed_2371_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_diag_2372_);
v___x_2389_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = lean_st_ref_set(v_a_2343_, v___x_2389_);
if (v_isShared_2366_ == 0)
{
v___x_2392_ = v___x_2365_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2362_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2362_);
lean_dec(v_a_2351_);
return v___x_2361_;
}
}
else
{
lean_dec(v_a_2351_);
return v___x_2361_;
}
}
else
{
lean_object* v_val_2400_; lean_object* v___x_2402_; 
lean_dec(v_a_2351_);
lean_dec_ref(v_inferType_2341_);
v_val_2400_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_val_2400_);
lean_dec_ref(v___x_2360_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v_val_2400_);
v___x_2402_ = v___x_2353_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_val_2400_);
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
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_inferType_2341_);
v_a_2405_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2350_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2350_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v___x_2413_; 
lean_dec_ref(v_e_2340_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
v___x_2413_ = lean_apply_5(v_inferType_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, lean_box(0));
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2414_, lean_object* v_inferType_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2414_, v_inferType_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___y_2429_; uint8_t v___y_2430_; lean_object* v___y_2431_; uint8_t v___y_2432_; lean_object* v___y_2433_; uint8_t v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; uint8_t v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; uint8_t v___y_2468_; lean_object* v___x_2526_; uint8_t v_transparency_2527_; uint8_t v___x_2528_; uint8_t v___x_2529_; 
v___x_2526_ = l_Lean_Meta_Context_config(v_a_2423_);
v_transparency_2527_ = lean_ctor_get_uint8(v___x_2526_, 9);
lean_dec_ref(v___x_2526_);
v___x_2528_ = 1;
v___x_2529_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2527_, v___x_2528_);
if (v___x_2529_ == 0)
{
v___y_2468_ = v_transparency_2527_;
goto v___jp_2467_;
}
else
{
v___y_2468_ = v___x_2528_;
goto v___jp_2467_;
}
v___jp_2428_:
{
lean_object* v___x_2440_; uint8_t v_foApprox_2441_; uint8_t v_ctxApprox_2442_; uint8_t v_quasiPatternApprox_2443_; uint8_t v_constApprox_2444_; uint8_t v_isDefEqStuckEx_2445_; uint8_t v_unificationHints_2446_; uint8_t v_proofIrrelevance_2447_; uint8_t v_assignSyntheticOpaque_2448_; uint8_t v_offsetCnstrs_2449_; uint8_t v_transparency_2450_; uint8_t v_univApprox_2451_; uint8_t v_zetaUnused_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2466_; 
v___x_2440_ = l_Lean_Meta_Context_config(v___y_2438_);
lean_dec_ref(v___y_2438_);
v_foApprox_2441_ = lean_ctor_get_uint8(v___x_2440_, 0);
v_ctxApprox_2442_ = lean_ctor_get_uint8(v___x_2440_, 1);
v_quasiPatternApprox_2443_ = lean_ctor_get_uint8(v___x_2440_, 2);
v_constApprox_2444_ = lean_ctor_get_uint8(v___x_2440_, 3);
v_isDefEqStuckEx_2445_ = lean_ctor_get_uint8(v___x_2440_, 4);
v_unificationHints_2446_ = lean_ctor_get_uint8(v___x_2440_, 5);
v_proofIrrelevance_2447_ = lean_ctor_get_uint8(v___x_2440_, 6);
v_assignSyntheticOpaque_2448_ = lean_ctor_get_uint8(v___x_2440_, 7);
v_offsetCnstrs_2449_ = lean_ctor_get_uint8(v___x_2440_, 8);
v_transparency_2450_ = lean_ctor_get_uint8(v___x_2440_, 9);
v_univApprox_2451_ = lean_ctor_get_uint8(v___x_2440_, 11);
v_zetaUnused_2452_ = lean_ctor_get_uint8(v___x_2440_, 17);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2454_ = v___x_2440_;
v_isShared_2455_ = v_isSharedCheck_2466_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v___x_2440_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2466_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
uint8_t v___x_2456_; uint8_t v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2460_; 
v___x_2456_ = 1;
v___x_2457_ = 0;
v___x_2458_ = 2;
if (v_isShared_2455_ == 0)
{
v___x_2460_ = v___x_2454_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 0, v_foApprox_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 1, v_ctxApprox_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 2, v_quasiPatternApprox_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 3, v_constApprox_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 4, v_isDefEqStuckEx_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 5, v_unificationHints_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 6, v_proofIrrelevance_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 7, v_assignSyntheticOpaque_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 8, v_offsetCnstrs_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 9, v_transparency_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 11, v_univApprox_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2465_, 17, v_zetaUnused_2452_);
v___x_2460_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
uint64_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_ctor_set_uint8(v___x_2460_, 10, v___x_2457_);
lean_ctor_set_uint8(v___x_2460_, 12, v___x_2456_);
lean_ctor_set_uint8(v___x_2460_, 13, v___x_2456_);
lean_ctor_set_uint8(v___x_2460_, 14, v___x_2458_);
lean_ctor_set_uint8(v___x_2460_, 15, v___x_2456_);
lean_ctor_set_uint8(v___x_2460_, 16, v___x_2456_);
lean_ctor_set_uint8(v___x_2460_, 18, v___x_2456_);
v___x_2461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2460_);
v___x_2462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set_uint64(v___x_2462_, sizeof(void*)*1, v___x_2461_);
lean_inc(v___y_2435_);
lean_inc(v___y_2439_);
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2431_);
lean_inc_ref(v___y_2436_);
lean_inc(v___y_2429_);
v___x_2463_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___y_2429_);
lean_ctor_set(v___x_2463_, 2, v___y_2436_);
lean_ctor_set(v___x_2463_, 3, v___y_2431_);
lean_ctor_set(v___x_2463_, 4, v___y_2433_);
lean_ctor_set(v___x_2463_, 5, v___y_2439_);
lean_ctor_set(v___x_2463_, 6, v___y_2435_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7, v___y_2434_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7 + 1, v___y_2437_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7 + 2, v___y_2432_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7 + 3, v___y_2430_);
lean_inc(v_a_2426_);
lean_inc_ref(v_a_2425_);
lean_inc(v_a_2424_);
v___x_2464_ = lean_apply_5(v_x_2422_, v___x_2463_, v_a_2424_, v_a_2425_, v_a_2426_, lean_box(0));
return v___x_2464_;
}
}
}
v___jp_2467_:
{
lean_object* v___x_2469_; uint8_t v_foApprox_2470_; uint8_t v_ctxApprox_2471_; uint8_t v_quasiPatternApprox_2472_; uint8_t v_constApprox_2473_; uint8_t v_isDefEqStuckEx_2474_; uint8_t v_unificationHints_2475_; uint8_t v_proofIrrelevance_2476_; uint8_t v_assignSyntheticOpaque_2477_; uint8_t v_offsetCnstrs_2478_; uint8_t v_etaStruct_2479_; uint8_t v_univApprox_2480_; uint8_t v_iota_2481_; uint8_t v_beta_2482_; uint8_t v_proj_2483_; uint8_t v_zeta_2484_; uint8_t v_zetaDelta_2485_; uint8_t v_zetaUnused_2486_; uint8_t v_zetaHave_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2525_; 
v___x_2469_ = l_Lean_Meta_Context_config(v_a_2423_);
v_foApprox_2470_ = lean_ctor_get_uint8(v___x_2469_, 0);
v_ctxApprox_2471_ = lean_ctor_get_uint8(v___x_2469_, 1);
v_quasiPatternApprox_2472_ = lean_ctor_get_uint8(v___x_2469_, 2);
v_constApprox_2473_ = lean_ctor_get_uint8(v___x_2469_, 3);
v_isDefEqStuckEx_2474_ = lean_ctor_get_uint8(v___x_2469_, 4);
v_unificationHints_2475_ = lean_ctor_get_uint8(v___x_2469_, 5);
v_proofIrrelevance_2476_ = lean_ctor_get_uint8(v___x_2469_, 6);
v_assignSyntheticOpaque_2477_ = lean_ctor_get_uint8(v___x_2469_, 7);
v_offsetCnstrs_2478_ = lean_ctor_get_uint8(v___x_2469_, 8);
v_etaStruct_2479_ = lean_ctor_get_uint8(v___x_2469_, 10);
v_univApprox_2480_ = lean_ctor_get_uint8(v___x_2469_, 11);
v_iota_2481_ = lean_ctor_get_uint8(v___x_2469_, 12);
v_beta_2482_ = lean_ctor_get_uint8(v___x_2469_, 13);
v_proj_2483_ = lean_ctor_get_uint8(v___x_2469_, 14);
v_zeta_2484_ = lean_ctor_get_uint8(v___x_2469_, 15);
v_zetaDelta_2485_ = lean_ctor_get_uint8(v___x_2469_, 16);
v_zetaUnused_2486_ = lean_ctor_get_uint8(v___x_2469_, 17);
v_zetaHave_2487_ = lean_ctor_get_uint8(v___x_2469_, 18);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2489_ = v___x_2469_;
v_isShared_2490_ = v_isSharedCheck_2525_;
goto v_resetjp_2488_;
}
else
{
lean_dec(v___x_2469_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2525_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
uint8_t v_trackZetaDelta_2491_; lean_object* v_zetaDeltaSet_2492_; lean_object* v_lctx_2493_; lean_object* v_localInstances_2494_; lean_object* v_defEqCtx_x3f_2495_; lean_object* v_synthPendingDepth_2496_; lean_object* v_canUnfold_x3f_2497_; uint8_t v_univApprox_2498_; uint8_t v_inTypeClassResolution_2499_; uint8_t v_cacheInferType_2500_; lean_object* v_config_2502_; 
v_trackZetaDelta_2491_ = lean_ctor_get_uint8(v_a_2423_, sizeof(void*)*7);
v_zetaDeltaSet_2492_ = lean_ctor_get(v_a_2423_, 1);
v_lctx_2493_ = lean_ctor_get(v_a_2423_, 2);
v_localInstances_2494_ = lean_ctor_get(v_a_2423_, 3);
v_defEqCtx_x3f_2495_ = lean_ctor_get(v_a_2423_, 4);
v_synthPendingDepth_2496_ = lean_ctor_get(v_a_2423_, 5);
v_canUnfold_x3f_2497_ = lean_ctor_get(v_a_2423_, 6);
v_univApprox_2498_ = lean_ctor_get_uint8(v_a_2423_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2499_ = lean_ctor_get_uint8(v_a_2423_, sizeof(void*)*7 + 2);
v_cacheInferType_2500_ = lean_ctor_get_uint8(v_a_2423_, sizeof(void*)*7 + 3);
if (v_isShared_2490_ == 0)
{
v_config_2502_ = v___x_2489_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 0, v_foApprox_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 1, v_ctxApprox_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 2, v_quasiPatternApprox_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 3, v_constApprox_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 4, v_isDefEqStuckEx_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 5, v_unificationHints_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 6, v_proofIrrelevance_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 7, v_assignSyntheticOpaque_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 8, v_offsetCnstrs_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 10, v_etaStruct_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 11, v_univApprox_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 12, v_iota_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 13, v_beta_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 14, v_proj_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 15, v_zeta_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 16, v_zetaDelta_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 17, v_zetaUnused_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2524_, 18, v_zetaHave_2487_);
v_config_2502_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
uint64_t v___x_2503_; uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; uint64_t v___x_2507_; uint64_t v_key_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v_beta_2512_; 
lean_ctor_set_uint8(v_config_2502_, 9, v___y_2468_);
v___x_2503_ = l_Lean_Meta_Context_configKey(v_a_2423_);
v___x_2504_ = 2ULL;
v___x_2505_ = lean_uint64_shift_right(v___x_2503_, v___x_2504_);
v___x_2506_ = lean_uint64_shift_left(v___x_2505_, v___x_2504_);
v___x_2507_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2468_);
v_key_2508_ = lean_uint64_lor(v___x_2506_, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2509_, 0, v_config_2502_);
lean_ctor_set_uint64(v___x_2509_, sizeof(void*)*1, v_key_2508_);
lean_inc(v_canUnfold_x3f_2497_);
lean_inc(v_synthPendingDepth_2496_);
lean_inc(v_defEqCtx_x3f_2495_);
lean_inc_ref(v_localInstances_2494_);
lean_inc_ref(v_lctx_2493_);
lean_inc(v_zetaDeltaSet_2492_);
v___x_2510_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v_zetaDeltaSet_2492_);
lean_ctor_set(v___x_2510_, 2, v_lctx_2493_);
lean_ctor_set(v___x_2510_, 3, v_localInstances_2494_);
lean_ctor_set(v___x_2510_, 4, v_defEqCtx_x3f_2495_);
lean_ctor_set(v___x_2510_, 5, v_synthPendingDepth_2496_);
lean_ctor_set(v___x_2510_, 6, v_canUnfold_x3f_2497_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*7, v_trackZetaDelta_2491_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*7 + 1, v_univApprox_2498_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2499_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*7 + 3, v_cacheInferType_2500_);
v___x_2511_ = l_Lean_Meta_Context_config(v___x_2510_);
v_beta_2512_ = lean_ctor_get_uint8(v___x_2511_, 13);
if (v_beta_2512_ == 0)
{
lean_dec_ref(v___x_2511_);
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
uint8_t v_iota_2513_; 
v_iota_2513_ = lean_ctor_get_uint8(v___x_2511_, 12);
if (v_iota_2513_ == 0)
{
lean_dec_ref(v___x_2511_);
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
uint8_t v_zeta_2514_; 
v_zeta_2514_ = lean_ctor_get_uint8(v___x_2511_, 15);
if (v_zeta_2514_ == 0)
{
lean_dec_ref(v___x_2511_);
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
uint8_t v_zetaHave_2515_; 
v_zetaHave_2515_ = lean_ctor_get_uint8(v___x_2511_, 18);
if (v_zetaHave_2515_ == 0)
{
lean_dec_ref(v___x_2511_);
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
uint8_t v_zetaDelta_2516_; 
v_zetaDelta_2516_ = lean_ctor_get_uint8(v___x_2511_, 16);
if (v_zetaDelta_2516_ == 0)
{
lean_dec_ref(v___x_2511_);
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
uint8_t v_etaStruct_2517_; uint8_t v_proj_2518_; uint8_t v___x_2519_; uint8_t v___x_2520_; 
v_etaStruct_2517_ = lean_ctor_get_uint8(v___x_2511_, 10);
v_proj_2518_ = lean_ctor_get_uint8(v___x_2511_, 14);
lean_dec_ref(v___x_2511_);
v___x_2519_ = 2;
v___x_2520_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
uint8_t v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = 0;
v___x_2522_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2517_, v___x_2521_);
if (v___x_2522_ == 0)
{
v___y_2429_ = v_zetaDeltaSet_2492_;
v___y_2430_ = v_cacheInferType_2500_;
v___y_2431_ = v_localInstances_2494_;
v___y_2432_ = v_inTypeClassResolution_2499_;
v___y_2433_ = v_defEqCtx_x3f_2495_;
v___y_2434_ = v_trackZetaDelta_2491_;
v___y_2435_ = v_canUnfold_x3f_2497_;
v___y_2436_ = v_lctx_2493_;
v___y_2437_ = v_univApprox_2498_;
v___y_2438_ = v___x_2510_;
v___y_2439_ = v_synthPendingDepth_2496_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2523_; 
lean_inc(v_a_2426_);
lean_inc_ref(v_a_2425_);
lean_inc(v_a_2424_);
v___x_2523_ = lean_apply_5(v_x_2422_, v___x_2510_, v_a_2424_, v_a_2425_, v_a_2426_, lean_box(0));
return v___x_2523_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2537_, lean_object* v_x_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___y_2545_; uint8_t v___y_2546_; lean_object* v___y_2547_; uint8_t v___y_2548_; lean_object* v___y_2549_; uint8_t v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; uint8_t v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2584_; lean_object* v___x_2642_; uint8_t v_transparency_2643_; uint8_t v___x_2644_; uint8_t v___x_2645_; 
v___x_2642_ = l_Lean_Meta_Context_config(v_a_2539_);
v_transparency_2643_ = lean_ctor_get_uint8(v___x_2642_, 9);
lean_dec_ref(v___x_2642_);
v___x_2644_ = 1;
v___x_2645_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
v___y_2584_ = v_transparency_2643_;
goto v___jp_2583_;
}
else
{
v___y_2584_ = v___x_2644_;
goto v___jp_2583_;
}
v___jp_2544_:
{
lean_object* v___x_2556_; uint8_t v_foApprox_2557_; uint8_t v_ctxApprox_2558_; uint8_t v_quasiPatternApprox_2559_; uint8_t v_constApprox_2560_; uint8_t v_isDefEqStuckEx_2561_; uint8_t v_unificationHints_2562_; uint8_t v_proofIrrelevance_2563_; uint8_t v_assignSyntheticOpaque_2564_; uint8_t v_offsetCnstrs_2565_; uint8_t v_transparency_2566_; uint8_t v_univApprox_2567_; uint8_t v_zetaUnused_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2582_; 
v___x_2556_ = l_Lean_Meta_Context_config(v___y_2554_);
lean_dec_ref(v___y_2554_);
v_foApprox_2557_ = lean_ctor_get_uint8(v___x_2556_, 0);
v_ctxApprox_2558_ = lean_ctor_get_uint8(v___x_2556_, 1);
v_quasiPatternApprox_2559_ = lean_ctor_get_uint8(v___x_2556_, 2);
v_constApprox_2560_ = lean_ctor_get_uint8(v___x_2556_, 3);
v_isDefEqStuckEx_2561_ = lean_ctor_get_uint8(v___x_2556_, 4);
v_unificationHints_2562_ = lean_ctor_get_uint8(v___x_2556_, 5);
v_proofIrrelevance_2563_ = lean_ctor_get_uint8(v___x_2556_, 6);
v_assignSyntheticOpaque_2564_ = lean_ctor_get_uint8(v___x_2556_, 7);
v_offsetCnstrs_2565_ = lean_ctor_get_uint8(v___x_2556_, 8);
v_transparency_2566_ = lean_ctor_get_uint8(v___x_2556_, 9);
v_univApprox_2567_ = lean_ctor_get_uint8(v___x_2556_, 11);
v_zetaUnused_2568_ = lean_ctor_get_uint8(v___x_2556_, 17);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2570_ = v___x_2556_;
v_isShared_2571_ = v_isSharedCheck_2582_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___x_2556_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2582_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___x_2572_; uint8_t v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2576_; 
v___x_2572_ = 1;
v___x_2573_ = 0;
v___x_2574_ = 2;
if (v_isShared_2571_ == 0)
{
v___x_2576_ = v___x_2570_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 0, v_foApprox_2557_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 1, v_ctxApprox_2558_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 2, v_quasiPatternApprox_2559_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 3, v_constApprox_2560_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 4, v_isDefEqStuckEx_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 5, v_unificationHints_2562_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 6, v_proofIrrelevance_2563_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 7, v_assignSyntheticOpaque_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 8, v_offsetCnstrs_2565_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 9, v_transparency_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 11, v_univApprox_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2581_, 17, v_zetaUnused_2568_);
v___x_2576_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
uint64_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_ctor_set_uint8(v___x_2576_, 10, v___x_2573_);
lean_ctor_set_uint8(v___x_2576_, 12, v___x_2572_);
lean_ctor_set_uint8(v___x_2576_, 13, v___x_2572_);
lean_ctor_set_uint8(v___x_2576_, 14, v___x_2574_);
lean_ctor_set_uint8(v___x_2576_, 15, v___x_2572_);
lean_ctor_set_uint8(v___x_2576_, 16, v___x_2572_);
lean_ctor_set_uint8(v___x_2576_, 18, v___x_2572_);
v___x_2577_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set_uint64(v___x_2578_, sizeof(void*)*1, v___x_2577_);
lean_inc(v___y_2551_);
lean_inc(v___y_2555_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2547_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2545_);
v___x_2579_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___y_2545_);
lean_ctor_set(v___x_2579_, 2, v___y_2552_);
lean_ctor_set(v___x_2579_, 3, v___y_2547_);
lean_ctor_set(v___x_2579_, 4, v___y_2549_);
lean_ctor_set(v___x_2579_, 5, v___y_2555_);
lean_ctor_set(v___x_2579_, 6, v___y_2551_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*7, v___y_2550_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*7 + 1, v___y_2553_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*7 + 2, v___y_2548_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*7 + 3, v___y_2546_);
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
v___x_2580_ = lean_apply_5(v_x_2538_, v___x_2579_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
return v___x_2580_;
}
}
}
v___jp_2583_:
{
lean_object* v___x_2585_; uint8_t v_foApprox_2586_; uint8_t v_ctxApprox_2587_; uint8_t v_quasiPatternApprox_2588_; uint8_t v_constApprox_2589_; uint8_t v_isDefEqStuckEx_2590_; uint8_t v_unificationHints_2591_; uint8_t v_proofIrrelevance_2592_; uint8_t v_assignSyntheticOpaque_2593_; uint8_t v_offsetCnstrs_2594_; uint8_t v_etaStruct_2595_; uint8_t v_univApprox_2596_; uint8_t v_iota_2597_; uint8_t v_beta_2598_; uint8_t v_proj_2599_; uint8_t v_zeta_2600_; uint8_t v_zetaDelta_2601_; uint8_t v_zetaUnused_2602_; uint8_t v_zetaHave_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2641_; 
v___x_2585_ = l_Lean_Meta_Context_config(v_a_2539_);
v_foApprox_2586_ = lean_ctor_get_uint8(v___x_2585_, 0);
v_ctxApprox_2587_ = lean_ctor_get_uint8(v___x_2585_, 1);
v_quasiPatternApprox_2588_ = lean_ctor_get_uint8(v___x_2585_, 2);
v_constApprox_2589_ = lean_ctor_get_uint8(v___x_2585_, 3);
v_isDefEqStuckEx_2590_ = lean_ctor_get_uint8(v___x_2585_, 4);
v_unificationHints_2591_ = lean_ctor_get_uint8(v___x_2585_, 5);
v_proofIrrelevance_2592_ = lean_ctor_get_uint8(v___x_2585_, 6);
v_assignSyntheticOpaque_2593_ = lean_ctor_get_uint8(v___x_2585_, 7);
v_offsetCnstrs_2594_ = lean_ctor_get_uint8(v___x_2585_, 8);
v_etaStruct_2595_ = lean_ctor_get_uint8(v___x_2585_, 10);
v_univApprox_2596_ = lean_ctor_get_uint8(v___x_2585_, 11);
v_iota_2597_ = lean_ctor_get_uint8(v___x_2585_, 12);
v_beta_2598_ = lean_ctor_get_uint8(v___x_2585_, 13);
v_proj_2599_ = lean_ctor_get_uint8(v___x_2585_, 14);
v_zeta_2600_ = lean_ctor_get_uint8(v___x_2585_, 15);
v_zetaDelta_2601_ = lean_ctor_get_uint8(v___x_2585_, 16);
v_zetaUnused_2602_ = lean_ctor_get_uint8(v___x_2585_, 17);
v_zetaHave_2603_ = lean_ctor_get_uint8(v___x_2585_, 18);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2605_ = v___x_2585_;
v_isShared_2606_ = v_isSharedCheck_2641_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v___x_2585_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2641_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
uint8_t v_trackZetaDelta_2607_; lean_object* v_zetaDeltaSet_2608_; lean_object* v_lctx_2609_; lean_object* v_localInstances_2610_; lean_object* v_defEqCtx_x3f_2611_; lean_object* v_synthPendingDepth_2612_; lean_object* v_canUnfold_x3f_2613_; uint8_t v_univApprox_2614_; uint8_t v_inTypeClassResolution_2615_; uint8_t v_cacheInferType_2616_; lean_object* v_config_2618_; 
v_trackZetaDelta_2607_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*7);
v_zetaDeltaSet_2608_ = lean_ctor_get(v_a_2539_, 1);
v_lctx_2609_ = lean_ctor_get(v_a_2539_, 2);
v_localInstances_2610_ = lean_ctor_get(v_a_2539_, 3);
v_defEqCtx_x3f_2611_ = lean_ctor_get(v_a_2539_, 4);
v_synthPendingDepth_2612_ = lean_ctor_get(v_a_2539_, 5);
v_canUnfold_x3f_2613_ = lean_ctor_get(v_a_2539_, 6);
v_univApprox_2614_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2615_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*7 + 2);
v_cacheInferType_2616_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*7 + 3);
if (v_isShared_2606_ == 0)
{
v_config_2618_ = v___x_2605_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 0, v_foApprox_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 1, v_ctxApprox_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 2, v_quasiPatternApprox_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 3, v_constApprox_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 4, v_isDefEqStuckEx_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 5, v_unificationHints_2591_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 6, v_proofIrrelevance_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 7, v_assignSyntheticOpaque_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 8, v_offsetCnstrs_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 10, v_etaStruct_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 11, v_univApprox_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 12, v_iota_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 13, v_beta_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 14, v_proj_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 15, v_zeta_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 16, v_zetaDelta_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 17, v_zetaUnused_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2640_, 18, v_zetaHave_2603_);
v_config_2618_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
uint64_t v___x_2619_; uint64_t v___x_2620_; uint64_t v___x_2621_; uint64_t v___x_2622_; uint64_t v___x_2623_; uint64_t v_key_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v_beta_2628_; 
lean_ctor_set_uint8(v_config_2618_, 9, v___y_2584_);
v___x_2619_ = l_Lean_Meta_Context_configKey(v_a_2539_);
v___x_2620_ = 2ULL;
v___x_2621_ = lean_uint64_shift_right(v___x_2619_, v___x_2620_);
v___x_2622_ = lean_uint64_shift_left(v___x_2621_, v___x_2620_);
v___x_2623_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2584_);
v_key_2624_ = lean_uint64_lor(v___x_2622_, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2625_, 0, v_config_2618_);
lean_ctor_set_uint64(v___x_2625_, sizeof(void*)*1, v_key_2624_);
lean_inc(v_canUnfold_x3f_2613_);
lean_inc(v_synthPendingDepth_2612_);
lean_inc(v_defEqCtx_x3f_2611_);
lean_inc_ref(v_localInstances_2610_);
lean_inc_ref(v_lctx_2609_);
lean_inc(v_zetaDeltaSet_2608_);
v___x_2626_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v_zetaDeltaSet_2608_);
lean_ctor_set(v___x_2626_, 2, v_lctx_2609_);
lean_ctor_set(v___x_2626_, 3, v_localInstances_2610_);
lean_ctor_set(v___x_2626_, 4, v_defEqCtx_x3f_2611_);
lean_ctor_set(v___x_2626_, 5, v_synthPendingDepth_2612_);
lean_ctor_set(v___x_2626_, 6, v_canUnfold_x3f_2613_);
lean_ctor_set_uint8(v___x_2626_, sizeof(void*)*7, v_trackZetaDelta_2607_);
lean_ctor_set_uint8(v___x_2626_, sizeof(void*)*7 + 1, v_univApprox_2614_);
lean_ctor_set_uint8(v___x_2626_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2615_);
lean_ctor_set_uint8(v___x_2626_, sizeof(void*)*7 + 3, v_cacheInferType_2616_);
v___x_2627_ = l_Lean_Meta_Context_config(v___x_2626_);
v_beta_2628_ = lean_ctor_get_uint8(v___x_2627_, 13);
if (v_beta_2628_ == 0)
{
lean_dec_ref(v___x_2627_);
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
uint8_t v_iota_2629_; 
v_iota_2629_ = lean_ctor_get_uint8(v___x_2627_, 12);
if (v_iota_2629_ == 0)
{
lean_dec_ref(v___x_2627_);
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
uint8_t v_zeta_2630_; 
v_zeta_2630_ = lean_ctor_get_uint8(v___x_2627_, 15);
if (v_zeta_2630_ == 0)
{
lean_dec_ref(v___x_2627_);
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
uint8_t v_zetaHave_2631_; 
v_zetaHave_2631_ = lean_ctor_get_uint8(v___x_2627_, 18);
if (v_zetaHave_2631_ == 0)
{
lean_dec_ref(v___x_2627_);
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
uint8_t v_zetaDelta_2632_; 
v_zetaDelta_2632_ = lean_ctor_get_uint8(v___x_2627_, 16);
if (v_zetaDelta_2632_ == 0)
{
lean_dec_ref(v___x_2627_);
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
uint8_t v_etaStruct_2633_; uint8_t v_proj_2634_; uint8_t v___x_2635_; uint8_t v___x_2636_; 
v_etaStruct_2633_ = lean_ctor_get_uint8(v___x_2627_, 10);
v_proj_2634_ = lean_ctor_get_uint8(v___x_2627_, 14);
lean_dec_ref(v___x_2627_);
v___x_2635_ = 2;
v___x_2636_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
uint8_t v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = 0;
v___x_2638_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2633_, v___x_2637_);
if (v___x_2638_ == 0)
{
v___y_2545_ = v_zetaDeltaSet_2608_;
v___y_2546_ = v_cacheInferType_2616_;
v___y_2547_ = v_localInstances_2610_;
v___y_2548_ = v_inTypeClassResolution_2615_;
v___y_2549_ = v_defEqCtx_x3f_2611_;
v___y_2550_ = v_trackZetaDelta_2607_;
v___y_2551_ = v_canUnfold_x3f_2613_;
v___y_2552_ = v_lctx_2609_;
v___y_2553_ = v_univApprox_2614_;
v___y_2554_ = v___x_2626_;
v___y_2555_ = v_synthPendingDepth_2612_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2639_; 
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
v___x_2639_ = lean_apply_5(v_x_2538_, v___x_2626_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
return v___x_2639_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2646_, lean_object* v_x_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2646_, v_x_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2654_, lean_object* v_x_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v_ks_2658_; lean_object* v_vs_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2688_; 
v_ks_2658_ = lean_ctor_get(v_x_2654_, 0);
v_vs_2659_ = lean_ctor_get(v_x_2654_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_x_2654_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2661_ = v_x_2654_;
v_isShared_2662_ = v_isSharedCheck_2688_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_vs_2659_);
lean_inc(v_ks_2658_);
lean_dec(v_x_2654_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2688_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___y_2664_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = lean_array_get_size(v_ks_2658_);
v___x_2677_ = lean_nat_dec_lt(v_x_2655_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_del_object(v___x_2661_);
lean_dec(v_x_2655_);
v___x_2678_ = lean_array_push(v_ks_2658_, v_x_2656_);
v___x_2679_ = lean_array_push(v_vs_2659_, v_x_2657_);
v___x_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
return v___x_2680_;
}
else
{
lean_object* v_expr_2681_; uint64_t v_configKey_2682_; lean_object* v_k_x27_2683_; lean_object* v_expr_2684_; uint64_t v_configKey_2685_; uint8_t v___x_2686_; 
v_expr_2681_ = lean_ctor_get(v_x_2656_, 0);
v_configKey_2682_ = lean_ctor_get_uint64(v_x_2656_, sizeof(void*)*1);
v_k_x27_2683_ = lean_array_fget_borrowed(v_ks_2658_, v_x_2655_);
v_expr_2684_ = lean_ctor_get(v_k_x27_2683_, 0);
v_configKey_2685_ = lean_ctor_get_uint64(v_k_x27_2683_, sizeof(void*)*1);
v___x_2686_ = lean_expr_equal(v_expr_2681_, v_expr_2684_);
if (v___x_2686_ == 0)
{
v___y_2664_ = v___x_2686_;
goto v___jp_2663_;
}
else
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_uint64_dec_eq(v_configKey_2682_, v_configKey_2685_);
v___y_2664_ = v___x_2687_;
goto v___jp_2663_;
}
}
v___jp_2663_:
{
if (v___y_2664_ == 0)
{
lean_object* v___x_2666_; 
if (v_isShared_2662_ == 0)
{
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_ks_2658_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_vs_2659_);
v___x_2666_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_add(v_x_2655_, v___x_2667_);
lean_dec(v_x_2655_);
v_x_2654_ = v___x_2666_;
v_x_2655_ = v___x_2668_;
goto _start;
}
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2671_ = lean_array_fset(v_ks_2658_, v_x_2655_, v_x_2656_);
v___x_2672_ = lean_array_fset(v_vs_2659_, v_x_2655_, v_x_2657_);
lean_dec(v_x_2655_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2672_);
lean_ctor_set(v___x_2661_, 0, v___x_2671_);
v___x_2674_ = v___x_2661_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(lean_object* v_n_2689_, lean_object* v_k_2690_, lean_object* v_v_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2689_, v___x_2692_, v_k_2690_, v_v_2691_);
return v___x_2693_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object* v_x_2695_, size_t v_x_2696_, size_t v_x_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
if (lean_obj_tag(v_x_2695_) == 0)
{
lean_object* v_es_2700_; size_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v_j_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_es_2700_ = lean_ctor_get(v_x_2695_, 0);
v___x_2701_ = ((size_t)5ULL);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2704_ = lean_usize_land(v_x_2696_, v___x_2703_);
v_j_2705_ = lean_usize_to_nat(v___x_2704_);
v___x_2706_ = lean_array_get_size(v_es_2700_);
v___x_2707_ = lean_nat_dec_lt(v_j_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_dec(v_j_2705_);
lean_dec(v_x_2699_);
lean_dec_ref(v_x_2698_);
return v_x_2695_;
}
else
{
lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2751_; 
lean_inc_ref(v_es_2700_);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_x_2695_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v_x_2695_, 0);
lean_dec(v_unused_2752_);
v___x_2709_ = v_x_2695_;
v_isShared_2710_ = v_isSharedCheck_2751_;
goto v_resetjp_2708_;
}
else
{
lean_dec(v_x_2695_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2751_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_v_2711_; lean_object* v___x_2712_; lean_object* v_xs_x27_2713_; lean_object* v___y_2715_; 
v_v_2711_ = lean_array_fget(v_es_2700_, v_j_2705_);
v___x_2712_ = lean_box(0);
v_xs_x27_2713_ = lean_array_fset(v_es_2700_, v_j_2705_, v___x_2712_);
switch(lean_obj_tag(v_v_2711_))
{
case 0:
{
lean_object* v_key_2720_; lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2738_; 
v_key_2720_ = lean_ctor_get(v_v_2711_, 0);
v_val_2721_ = lean_ctor_get(v_v_2711_, 1);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_v_2711_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2723_ = v_v_2711_;
v_isShared_2724_ = v_isSharedCheck_2738_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_inc(v_key_2720_);
lean_dec(v_v_2711_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2738_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
uint8_t v___y_2726_; lean_object* v_expr_2732_; uint64_t v_configKey_2733_; lean_object* v_expr_2734_; uint64_t v_configKey_2735_; uint8_t v___x_2736_; 
v_expr_2732_ = lean_ctor_get(v_x_2698_, 0);
v_configKey_2733_ = lean_ctor_get_uint64(v_x_2698_, sizeof(void*)*1);
v_expr_2734_ = lean_ctor_get(v_key_2720_, 0);
v_configKey_2735_ = lean_ctor_get_uint64(v_key_2720_, sizeof(void*)*1);
v___x_2736_ = lean_expr_equal(v_expr_2732_, v_expr_2734_);
if (v___x_2736_ == 0)
{
v___y_2726_ = v___x_2736_;
goto v___jp_2725_;
}
else
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_uint64_dec_eq(v_configKey_2733_, v_configKey_2735_);
v___y_2726_ = v___x_2737_;
goto v___jp_2725_;
}
v___jp_2725_:
{
if (v___y_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_del_object(v___x_2723_);
v___x_2727_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2720_, v_val_2721_, v_x_2698_, v_x_2699_);
v___x_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
v___y_2715_ = v___x_2728_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_val_2721_);
lean_dec(v_key_2720_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 1, v_x_2699_);
lean_ctor_set(v___x_2723_, 0, v_x_2698_);
v___x_2730_ = v___x_2723_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_x_2698_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_x_2699_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
v___y_2715_ = v___x_2730_;
goto v___jp_2714_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2749_; 
v_node_2739_ = lean_ctor_get(v_v_2711_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_v_2711_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2741_ = v_v_2711_;
v_isShared_2742_ = v_isSharedCheck_2749_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_node_2739_);
lean_dec(v_v_2711_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2749_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2743_ = lean_usize_shift_right(v_x_2696_, v___x_2701_);
v___x_2744_ = lean_usize_add(v_x_2697_, v___x_2702_);
v___x_2745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_node_2739_, v___x_2743_, v___x_2744_, v_x_2698_, v_x_2699_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2745_);
v___x_2747_ = v___x_2741_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
v___y_2715_ = v___x_2747_;
goto v___jp_2714_;
}
}
}
default: 
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_x_2698_);
lean_ctor_set(v___x_2750_, 1, v_x_2699_);
v___y_2715_ = v___x_2750_;
goto v___jp_2714_;
}
}
v___jp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_array_fset(v_xs_x27_2713_, v_j_2705_, v___y_2715_);
lean_dec(v_j_2705_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2716_);
v___x_2718_ = v___x_2709_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
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
else
{
lean_object* v_ks_2753_; lean_object* v_vs_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2774_; 
v_ks_2753_ = lean_ctor_get(v_x_2695_, 0);
v_vs_2754_ = lean_ctor_get(v_x_2695_, 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_x_2695_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2756_ = v_x_2695_;
v_isShared_2757_ = v_isSharedCheck_2774_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_vs_2754_);
lean_inc(v_ks_2753_);
lean_dec(v_x_2695_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2774_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_ks_2753_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_vs_2754_);
v___x_2759_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v_newNode_2760_; uint8_t v___y_2762_; size_t v___x_2768_; uint8_t v___x_2769_; 
v_newNode_2760_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v___x_2759_, v_x_2698_, v_x_2699_);
v___x_2768_ = ((size_t)7ULL);
v___x_2769_ = lean_usize_dec_le(v___x_2768_, v_x_2697_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2770_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2760_);
v___x_2771_ = lean_unsigned_to_nat(4u);
v___x_2772_ = lean_nat_dec_lt(v___x_2770_, v___x_2771_);
lean_dec(v___x_2770_);
v___y_2762_ = v___x_2772_;
goto v___jp_2761_;
}
else
{
v___y_2762_ = v___x_2769_;
goto v___jp_2761_;
}
v___jp_2761_:
{
if (v___y_2762_ == 0)
{
lean_object* v_ks_2763_; lean_object* v_vs_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_ks_2763_ = lean_ctor_get(v_newNode_2760_, 0);
lean_inc_ref(v_ks_2763_);
v_vs_2764_ = lean_ctor_get(v_newNode_2760_, 1);
lean_inc_ref(v_vs_2764_);
lean_dec_ref(v_newNode_2760_);
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0);
v___x_2767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_x_2697_, v_ks_2763_, v_vs_2764_, v___x_2765_, v___x_2766_);
lean_dec_ref(v_vs_2764_);
lean_dec_ref(v_ks_2763_);
return v___x_2767_;
}
else
{
return v_newNode_2760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(size_t v_depth_2775_, lean_object* v_keys_2776_, lean_object* v_vals_2777_, lean_object* v_i_2778_, lean_object* v_entries_2779_){
_start:
{
lean_object* v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = lean_array_get_size(v_keys_2776_);
v___x_2781_ = lean_nat_dec_lt(v_i_2778_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_dec(v_i_2778_);
return v_entries_2779_;
}
else
{
lean_object* v_k_2782_; lean_object* v_expr_2783_; uint64_t v_configKey_2784_; lean_object* v_v_2785_; uint64_t v___x_2786_; uint64_t v___x_2787_; size_t v_h_2788_; size_t v___x_2789_; lean_object* v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; size_t v___x_2793_; size_t v_h_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_k_2782_ = lean_array_fget_borrowed(v_keys_2776_, v_i_2778_);
v_expr_2783_ = lean_ctor_get(v_k_2782_, 0);
v_configKey_2784_ = lean_ctor_get_uint64(v_k_2782_, sizeof(void*)*1);
v_v_2785_ = lean_array_fget_borrowed(v_vals_2777_, v_i_2778_);
v___x_2786_ = l_Lean_Expr_hash(v_expr_2783_);
v___x_2787_ = lean_uint64_mix_hash(v___x_2786_, v_configKey_2784_);
v_h_2788_ = lean_uint64_to_usize(v___x_2787_);
v___x_2789_ = ((size_t)5ULL);
v___x_2790_ = lean_unsigned_to_nat(1u);
v___x_2791_ = ((size_t)1ULL);
v___x_2792_ = lean_usize_sub(v_depth_2775_, v___x_2791_);
v___x_2793_ = lean_usize_mul(v___x_2789_, v___x_2792_);
v_h_2794_ = lean_usize_shift_right(v_h_2788_, v___x_2793_);
v___x_2795_ = lean_nat_add(v_i_2778_, v___x_2790_);
lean_dec(v_i_2778_);
lean_inc(v_v_2785_);
lean_inc(v_k_2782_);
v___x_2796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_entries_2779_, v_h_2794_, v_depth_2775_, v_k_2782_, v_v_2785_);
v_i_2778_ = v___x_2795_;
v_entries_2779_ = v___x_2796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_2798_, lean_object* v_keys_2799_, lean_object* v_vals_2800_, lean_object* v_i_2801_, lean_object* v_entries_2802_){
_start:
{
size_t v_depth_boxed_2803_; lean_object* v_res_2804_; 
v_depth_boxed_2803_ = lean_unbox_usize(v_depth_2798_);
lean_dec(v_depth_2798_);
v_res_2804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2803_, v_keys_2799_, v_vals_2800_, v_i_2801_, v_entries_2802_);
lean_dec_ref(v_vals_2800_);
lean_dec_ref(v_keys_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object* v_x_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_, lean_object* v_x_2809_){
_start:
{
size_t v_x_2105__boxed_2810_; size_t v_x_2106__boxed_2811_; lean_object* v_res_2812_; 
v_x_2105__boxed_2810_ = lean_unbox_usize(v_x_2806_);
lean_dec(v_x_2806_);
v_x_2106__boxed_2811_ = lean_unbox_usize(v_x_2807_);
lean_dec(v_x_2807_);
v_res_2812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2805_, v_x_2105__boxed_2810_, v_x_2106__boxed_2811_, v_x_2808_, v_x_2809_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_){
_start:
{
lean_object* v_expr_2816_; uint64_t v_configKey_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v_expr_2816_ = lean_ctor_get(v_x_2814_, 0);
v_configKey_2817_ = lean_ctor_get_uint64(v_x_2814_, sizeof(void*)*1);
v___x_2818_ = l_Lean_Expr_hash(v_expr_2816_);
v___x_2819_ = lean_uint64_mix_hash(v___x_2818_, v_configKey_2817_);
v___x_2820_ = lean_uint64_to_usize(v___x_2819_);
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2813_, v___x_2820_, v___x_2821_, v_x_2814_, v_x_2815_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2823_, lean_object* v_vals_2824_, lean_object* v_i_2825_, lean_object* v_k_2826_){
_start:
{
uint8_t v___y_2828_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2834_ = lean_array_get_size(v_keys_2823_);
v___x_2835_ = lean_nat_dec_lt(v_i_2825_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; 
lean_dec(v_i_2825_);
v___x_2836_ = lean_box(0);
return v___x_2836_;
}
else
{
lean_object* v_expr_2837_; uint64_t v_configKey_2838_; lean_object* v_k_x27_2839_; lean_object* v_expr_2840_; uint64_t v_configKey_2841_; uint8_t v___x_2842_; 
v_expr_2837_ = lean_ctor_get(v_k_2826_, 0);
v_configKey_2838_ = lean_ctor_get_uint64(v_k_2826_, sizeof(void*)*1);
v_k_x27_2839_ = lean_array_fget_borrowed(v_keys_2823_, v_i_2825_);
v_expr_2840_ = lean_ctor_get(v_k_x27_2839_, 0);
v_configKey_2841_ = lean_ctor_get_uint64(v_k_x27_2839_, sizeof(void*)*1);
v___x_2842_ = lean_expr_equal(v_expr_2837_, v_expr_2840_);
if (v___x_2842_ == 0)
{
v___y_2828_ = v___x_2842_;
goto v___jp_2827_;
}
else
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_uint64_dec_eq(v_configKey_2838_, v_configKey_2841_);
v___y_2828_ = v___x_2843_;
goto v___jp_2827_;
}
}
v___jp_2827_:
{
if (v___y_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = lean_nat_add(v_i_2825_, v___x_2829_);
lean_dec(v_i_2825_);
v_i_2825_ = v___x_2830_;
goto _start;
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_array_fget_borrowed(v_vals_2824_, v_i_2825_);
lean_dec(v_i_2825_);
lean_inc(v___x_2832_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2844_, lean_object* v_vals_2845_, lean_object* v_i_2846_, lean_object* v_k_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_2844_, v_vals_2845_, v_i_2846_, v_k_2847_);
lean_dec_ref(v_k_2847_);
lean_dec_ref(v_vals_2845_);
lean_dec_ref(v_keys_2844_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object* v_x_2849_, size_t v_x_2850_, lean_object* v_x_2851_){
_start:
{
if (lean_obj_tag(v_x_2849_) == 0)
{
lean_object* v_es_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2880_; 
v_es_2852_ = lean_ctor_get(v_x_2849_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_x_2849_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2854_ = v_x_2849_;
v_isShared_2855_ = v_isSharedCheck_2880_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_es_2852_);
lean_dec(v_x_2849_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2880_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; size_t v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; lean_object* v_j_2860_; lean_object* v___x_2861_; 
v___x_2856_ = lean_box(2);
v___x_2857_ = ((size_t)5ULL);
v___x_2858_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2859_ = lean_usize_land(v_x_2850_, v___x_2858_);
v_j_2860_ = lean_usize_to_nat(v___x_2859_);
v___x_2861_ = lean_array_get(v___x_2856_, v_es_2852_, v_j_2860_);
lean_dec(v_j_2860_);
lean_dec_ref(v_es_2852_);
switch(lean_obj_tag(v___x_2861_))
{
case 0:
{
lean_object* v_key_2862_; lean_object* v_val_2863_; uint8_t v___y_2865_; lean_object* v_expr_2870_; uint64_t v_configKey_2871_; lean_object* v_expr_2872_; uint64_t v_configKey_2873_; uint8_t v___x_2874_; 
v_key_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_key_2862_);
v_val_2863_ = lean_ctor_get(v___x_2861_, 1);
lean_inc(v_val_2863_);
lean_dec_ref(v___x_2861_);
v_expr_2870_ = lean_ctor_get(v_x_2851_, 0);
v_configKey_2871_ = lean_ctor_get_uint64(v_x_2851_, sizeof(void*)*1);
v_expr_2872_ = lean_ctor_get(v_key_2862_, 0);
lean_inc_ref(v_expr_2872_);
v_configKey_2873_ = lean_ctor_get_uint64(v_key_2862_, sizeof(void*)*1);
lean_dec(v_key_2862_);
v___x_2874_ = lean_expr_equal(v_expr_2870_, v_expr_2872_);
lean_dec_ref(v_expr_2872_);
if (v___x_2874_ == 0)
{
v___y_2865_ = v___x_2874_;
goto v___jp_2864_;
}
else
{
uint8_t v___x_2875_; 
v___x_2875_ = lean_uint64_dec_eq(v_configKey_2871_, v_configKey_2873_);
v___y_2865_ = v___x_2875_;
goto v___jp_2864_;
}
v___jp_2864_:
{
if (v___y_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v_val_2863_);
lean_del_object(v___x_2854_);
v___x_2866_ = lean_box(0);
return v___x_2866_;
}
else
{
lean_object* v___x_2868_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set_tag(v___x_2854_, 1);
lean_ctor_set(v___x_2854_, 0, v_val_2863_);
v___x_2868_ = v___x_2854_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_val_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
case 1:
{
lean_object* v_node_2876_; size_t v___x_2877_; 
lean_del_object(v___x_2854_);
v_node_2876_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_node_2876_);
lean_dec_ref(v___x_2861_);
v___x_2877_ = lean_usize_shift_right(v_x_2850_, v___x_2857_);
v_x_2849_ = v_node_2876_;
v_x_2850_ = v___x_2877_;
goto _start;
}
default: 
{
lean_object* v___x_2879_; 
lean_del_object(v___x_2854_);
v___x_2879_ = lean_box(0);
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_ks_2881_; lean_object* v_vs_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_ks_2881_ = lean_ctor_get(v_x_2849_, 0);
lean_inc_ref(v_ks_2881_);
v_vs_2882_ = lean_ctor_get(v_x_2849_, 1);
lean_inc_ref(v_vs_2882_);
lean_dec_ref(v_x_2849_);
v___x_2883_ = lean_unsigned_to_nat(0u);
v___x_2884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_ks_2881_, v_vs_2882_, v___x_2883_, v_x_2851_);
lean_dec_ref(v_vs_2882_);
lean_dec_ref(v_ks_2881_);
return v___x_2884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object* v_x_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_){
_start:
{
size_t v_x_2320__boxed_2888_; lean_object* v_res_2889_; 
v_x_2320__boxed_2888_ = lean_unbox_usize(v_x_2886_);
lean_dec(v_x_2886_);
v_res_2889_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2885_, v_x_2320__boxed_2888_, v_x_2887_);
lean_dec_ref(v_x_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object* v_x_2890_, lean_object* v_x_2891_){
_start:
{
lean_object* v_expr_2892_; uint64_t v_configKey_2893_; uint64_t v___x_2894_; uint64_t v___x_2895_; size_t v___x_2896_; lean_object* v___x_2897_; 
v_expr_2892_ = lean_ctor_get(v_x_2891_, 0);
v_configKey_2893_ = lean_ctor_get_uint64(v_x_2891_, sizeof(void*)*1);
v___x_2894_ = l_Lean_Expr_hash(v_expr_2892_);
v___x_2895_ = lean_uint64_mix_hash(v___x_2894_, v_configKey_2893_);
v___x_2896_ = lean_uint64_to_usize(v___x_2895_);
v___x_2897_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2890_, v___x_2896_, v_x_2891_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_2898_, v_x_2899_);
lean_dec_ref(v_x_2899_);
return v_res_2900_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_2903_ = l_Lean_stringToMessageData(v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
switch(lean_obj_tag(v_e_2904_))
{
case 0:
{
lean_object* v_deBruijnIndex_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_deBruijnIndex_2910_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_deBruijnIndex_2910_);
lean_dec_ref(v_e_2904_);
v___x_2911_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_2912_ = l_Lean_mkBVar(v_deBruijnIndex_2910_);
v___x_2913_ = l_Lean_MessageData_ofExpr(v___x_2912_);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2911_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2914_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2915_;
}
case 1:
{
lean_object* v_fvarId_2916_; lean_object* v___x_2917_; 
v_fvarId_2916_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_fvarId_2916_);
lean_dec_ref(v_e_2904_);
v___x_2917_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2916_, v_a_2905_, v_a_2907_, v_a_2908_);
return v___x_2917_;
}
case 2:
{
lean_object* v_mvarId_2918_; lean_object* v___x_2919_; 
v_mvarId_2918_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_mvarId_2918_);
lean_dec_ref(v_e_2904_);
v___x_2919_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2918_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2919_;
}
case 3:
{
lean_object* v_u_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_u_2920_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_u_2920_);
lean_dec_ref(v_e_2904_);
v___x_2921_ = l_Lean_Level_succ___override(v_u_2920_);
v___x_2922_ = l_Lean_mkSort(v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
case 4:
{
lean_object* v_us_2924_; 
v_us_2924_ = lean_ctor_get(v_e_2904_, 1);
lean_inc(v_us_2924_);
if (lean_obj_tag(v_us_2924_) == 0)
{
lean_object* v_declName_2925_; lean_object* v___x_2926_; 
v_declName_2925_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_declName_2925_);
lean_dec_ref(v_e_2904_);
v___x_2926_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2925_, v_us_2924_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2926_;
}
else
{
uint8_t v_cacheInferType_2927_; 
v_cacheInferType_2927_ = lean_ctor_get_uint8(v_a_2905_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2927_ == 0)
{
lean_object* v_declName_2928_; lean_object* v___x_2929_; 
v_declName_2928_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_declName_2928_);
lean_dec_ref(v_e_2904_);
v___x_2929_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2928_, v_us_2924_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2929_;
}
else
{
lean_object* v_declName_2930_; uint8_t v___x_2931_; 
v_declName_2930_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_declName_2930_);
v___x_2931_ = l_Lean_Expr_hasMVar(v_e_2904_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2984_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2984_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2984_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v_cache_2938_; lean_object* v_inferType_2939_; lean_object* v___x_2940_; 
v___x_2937_ = lean_st_ref_get(v_a_2906_);
v_cache_2938_ = lean_ctor_get(v___x_2937_, 1);
lean_inc_ref(v_cache_2938_);
lean_dec(v___x_2937_);
v_inferType_2939_ = lean_ctor_get(v_cache_2938_, 0);
lean_inc_ref(v_inferType_2939_);
lean_dec_ref(v_cache_2938_);
v___x_2940_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_2939_, v_a_2933_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2941_; 
lean_del_object(v___x_2935_);
v___x_2941_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2930_, v_us_2924_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; uint8_t v___x_2943_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
v___x_2943_ = l_Lean_Expr_hasMVar(v_a_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2978_; 
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v___x_2941_, 0);
lean_dec(v_unused_2979_);
v___x_2945_ = v___x_2941_;
v_isShared_2946_ = v_isSharedCheck_2978_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v___x_2941_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2978_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v_cache_2948_; lean_object* v_mctx_2949_; lean_object* v_zetaDeltaFVarIds_2950_; lean_object* v_postponed_2951_; lean_object* v_diag_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2977_; 
v___x_2947_ = lean_st_ref_take(v_a_2906_);
v_cache_2948_ = lean_ctor_get(v___x_2947_, 1);
v_mctx_2949_ = lean_ctor_get(v___x_2947_, 0);
v_zetaDeltaFVarIds_2950_ = lean_ctor_get(v___x_2947_, 2);
v_postponed_2951_ = lean_ctor_get(v___x_2947_, 3);
v_diag_2952_ = lean_ctor_get(v___x_2947_, 4);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2954_ = v___x_2947_;
v_isShared_2955_ = v_isSharedCheck_2977_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_diag_2952_);
lean_inc(v_postponed_2951_);
lean_inc(v_zetaDeltaFVarIds_2950_);
lean_inc(v_cache_2948_);
lean_inc(v_mctx_2949_);
lean_dec(v___x_2947_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2977_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_inferType_2956_; lean_object* v_funInfo_2957_; lean_object* v_synthInstance_2958_; lean_object* v_whnf_2959_; lean_object* v_defEqTrans_2960_; lean_object* v_defEqPerm_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2976_; 
v_inferType_2956_ = lean_ctor_get(v_cache_2948_, 0);
v_funInfo_2957_ = lean_ctor_get(v_cache_2948_, 1);
v_synthInstance_2958_ = lean_ctor_get(v_cache_2948_, 2);
v_whnf_2959_ = lean_ctor_get(v_cache_2948_, 3);
v_defEqTrans_2960_ = lean_ctor_get(v_cache_2948_, 4);
v_defEqPerm_2961_ = lean_ctor_get(v_cache_2948_, 5);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_cache_2948_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2963_ = v_cache_2948_;
v_isShared_2964_ = v_isSharedCheck_2976_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_defEqPerm_2961_);
lean_inc(v_defEqTrans_2960_);
lean_inc(v_whnf_2959_);
lean_inc(v_synthInstance_2958_);
lean_inc(v_funInfo_2957_);
lean_inc(v_inferType_2956_);
lean_dec(v_cache_2948_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2976_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_inc(v_a_2942_);
v___x_2965_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_2956_, v_a_2933_, v_a_2942_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_funInfo_2957_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_synthInstance_2958_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_whnf_2959_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_defEqTrans_2960_);
lean_ctor_set(v_reuseFailAlloc_2975_, 5, v_defEqPerm_2961_);
v___x_2967_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2967_);
v___x_2969_ = v___x_2954_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_mctx_2949_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_zetaDeltaFVarIds_2950_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_postponed_2951_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_diag_2952_);
v___x_2969_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2970_ = lean_st_ref_set(v_a_2906_, v___x_2969_);
if (v_isShared_2946_ == 0)
{
v___x_2972_ = v___x_2945_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2942_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2942_);
lean_dec(v_a_2933_);
return v___x_2941_;
}
}
else
{
lean_dec(v_a_2933_);
return v___x_2941_;
}
}
else
{
lean_object* v_val_2980_; lean_object* v___x_2982_; 
lean_dec(v_a_2933_);
lean_dec(v_declName_2930_);
lean_dec(v_us_2924_);
v_val_2980_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_val_2980_);
lean_dec_ref(v___x_2940_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v_val_2980_);
v___x_2982_ = v___x_2935_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_val_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_declName_2930_);
lean_dec(v_us_2924_);
v_a_2985_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2932_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2932_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v___x_2993_; 
lean_dec_ref(v_e_2904_);
v___x_2993_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2930_, v_us_2924_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_2993_;
}
}
}
}
case 5:
{
lean_object* v_fn_2994_; uint8_t v_cacheInferType_2995_; lean_object* v_nargs_2996_; lean_object* v___x_2997_; lean_object* v_dummy_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_fn_2994_ = lean_ctor_get(v_e_2904_, 0);
v_cacheInferType_2995_ = lean_ctor_get_uint8(v_a_2905_, sizeof(void*)*7 + 3);
v_nargs_2996_ = l_Lean_Expr_getAppNumArgs(v_e_2904_);
v___x_2997_ = l_Lean_Expr_getAppFn(v_fn_2994_);
v_dummy_2998_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_2996_);
v___x_2999_ = lean_mk_array(v_nargs_2996_, v_dummy_2998_);
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = lean_nat_sub(v_nargs_2996_, v___x_3000_);
lean_dec(v_nargs_2996_);
lean_inc_ref(v_e_2904_);
v___x_3002_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2904_, v___x_2999_, v___x_3001_);
if (v_cacheInferType_2995_ == 0)
{
lean_object* v___x_3003_; 
lean_dec_ref(v_e_2904_);
v___x_3003_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_2997_, v___x_3002_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
lean_dec_ref(v___x_3002_);
return v___x_3003_;
}
else
{
uint8_t v___x_3004_; 
v___x_3004_ = l_Lean_Expr_hasMVar(v_e_2904_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2904_, v_a_2905_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3057_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3057_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3057_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v_cache_3011_; lean_object* v_inferType_3012_; lean_object* v___x_3013_; 
v___x_3010_ = lean_st_ref_get(v_a_2906_);
v_cache_3011_ = lean_ctor_get(v___x_3010_, 1);
lean_inc_ref(v_cache_3011_);
lean_dec(v___x_3010_);
v_inferType_3012_ = lean_ctor_get(v_cache_3011_, 0);
lean_inc_ref(v_inferType_3012_);
lean_dec_ref(v_cache_3011_);
v___x_3013_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3012_, v_a_3006_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; 
lean_del_object(v___x_3008_);
v___x_3014_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_2997_, v___x_3002_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
lean_dec_ref(v___x_3002_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; uint8_t v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
v___x_3016_ = l_Lean_Expr_hasMVar(v_a_3015_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3051_; 
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3052_);
v___x_3018_ = v___x_3014_;
v_isShared_3019_ = v_isSharedCheck_3051_;
goto v_resetjp_3017_;
}
else
{
lean_dec(v___x_3014_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3051_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v_cache_3021_; lean_object* v_mctx_3022_; lean_object* v_zetaDeltaFVarIds_3023_; lean_object* v_postponed_3024_; lean_object* v_diag_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3050_; 
v___x_3020_ = lean_st_ref_take(v_a_2906_);
v_cache_3021_ = lean_ctor_get(v___x_3020_, 1);
v_mctx_3022_ = lean_ctor_get(v___x_3020_, 0);
v_zetaDeltaFVarIds_3023_ = lean_ctor_get(v___x_3020_, 2);
v_postponed_3024_ = lean_ctor_get(v___x_3020_, 3);
v_diag_3025_ = lean_ctor_get(v___x_3020_, 4);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3027_ = v___x_3020_;
v_isShared_3028_ = v_isSharedCheck_3050_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_diag_3025_);
lean_inc(v_postponed_3024_);
lean_inc(v_zetaDeltaFVarIds_3023_);
lean_inc(v_cache_3021_);
lean_inc(v_mctx_3022_);
lean_dec(v___x_3020_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3050_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_inferType_3029_; lean_object* v_funInfo_3030_; lean_object* v_synthInstance_3031_; lean_object* v_whnf_3032_; lean_object* v_defEqTrans_3033_; lean_object* v_defEqPerm_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3049_; 
v_inferType_3029_ = lean_ctor_get(v_cache_3021_, 0);
v_funInfo_3030_ = lean_ctor_get(v_cache_3021_, 1);
v_synthInstance_3031_ = lean_ctor_get(v_cache_3021_, 2);
v_whnf_3032_ = lean_ctor_get(v_cache_3021_, 3);
v_defEqTrans_3033_ = lean_ctor_get(v_cache_3021_, 4);
v_defEqPerm_3034_ = lean_ctor_get(v_cache_3021_, 5);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_cache_3021_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3036_ = v_cache_3021_;
v_isShared_3037_ = v_isSharedCheck_3049_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_defEqPerm_3034_);
lean_inc(v_defEqTrans_3033_);
lean_inc(v_whnf_3032_);
lean_inc(v_synthInstance_3031_);
lean_inc(v_funInfo_3030_);
lean_inc(v_inferType_3029_);
lean_dec(v_cache_3021_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3049_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_inc(v_a_3015_);
v___x_3038_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3029_, v_a_3006_, v_a_3015_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3038_);
v___x_3040_ = v___x_3036_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_funInfo_3030_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_synthInstance_3031_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_whnf_3032_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_defEqTrans_3033_);
lean_ctor_set(v_reuseFailAlloc_3048_, 5, v_defEqPerm_3034_);
v___x_3040_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___x_3040_);
v___x_3042_ = v___x_3027_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_mctx_3022_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_zetaDeltaFVarIds_3023_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_postponed_3024_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_diag_3025_);
v___x_3042_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3043_ = lean_st_ref_set(v_a_2906_, v___x_3042_);
if (v_isShared_3019_ == 0)
{
v___x_3045_ = v___x_3018_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3015_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3015_);
lean_dec(v_a_3006_);
return v___x_3014_;
}
}
else
{
lean_dec(v_a_3006_);
return v___x_3014_;
}
}
else
{
lean_object* v_val_3053_; lean_object* v___x_3055_; 
lean_dec(v_a_3006_);
lean_dec_ref(v___x_3002_);
lean_dec_ref(v___x_2997_);
v_val_3053_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_val_3053_);
lean_dec_ref(v___x_3013_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v_val_3053_);
v___x_3055_ = v___x_3008_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_val_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v___x_3002_);
lean_dec_ref(v___x_2997_);
v_a_3058_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3005_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3005_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v___x_3066_; 
lean_dec_ref(v_e_2904_);
v___x_3066_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_2997_, v___x_3002_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
lean_dec_ref(v___x_3002_);
return v___x_3066_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3067_; 
v_cacheInferType_3067_ = lean_ctor_get_uint8(v_a_2905_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3067_ == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_3068_;
}
else
{
uint8_t v___x_3069_; 
v___x_3069_ = l_Lean_Expr_hasMVar(v_e_2904_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
lean_inc_ref(v_e_2904_);
v___x_3070_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2904_, v_a_2905_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3122_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3122_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3122_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v_cache_3076_; lean_object* v_inferType_3077_; lean_object* v___x_3078_; 
v___x_3075_ = lean_st_ref_get(v_a_2906_);
v_cache_3076_ = lean_ctor_get(v___x_3075_, 1);
lean_inc_ref(v_cache_3076_);
lean_dec(v___x_3075_);
v_inferType_3077_ = lean_ctor_get(v_cache_3076_, 0);
lean_inc_ref(v_inferType_3077_);
lean_dec_ref(v_cache_3076_);
v___x_3078_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3077_, v_a_3071_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v___x_3079_; 
lean_del_object(v___x_3073_);
v___x_3079_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; uint8_t v___x_3081_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
v___x_3081_ = l_Lean_Expr_hasMVar(v_a_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3116_; 
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3079_, 0);
lean_dec(v_unused_3117_);
v___x_3083_ = v___x_3079_;
v_isShared_3084_ = v_isSharedCheck_3116_;
goto v_resetjp_3082_;
}
else
{
lean_dec(v___x_3079_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3116_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v_cache_3086_; lean_object* v_mctx_3087_; lean_object* v_zetaDeltaFVarIds_3088_; lean_object* v_postponed_3089_; lean_object* v_diag_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3115_; 
v___x_3085_ = lean_st_ref_take(v_a_2906_);
v_cache_3086_ = lean_ctor_get(v___x_3085_, 1);
v_mctx_3087_ = lean_ctor_get(v___x_3085_, 0);
v_zetaDeltaFVarIds_3088_ = lean_ctor_get(v___x_3085_, 2);
v_postponed_3089_ = lean_ctor_get(v___x_3085_, 3);
v_diag_3090_ = lean_ctor_get(v___x_3085_, 4);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3092_ = v___x_3085_;
v_isShared_3093_ = v_isSharedCheck_3115_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_diag_3090_);
lean_inc(v_postponed_3089_);
lean_inc(v_zetaDeltaFVarIds_3088_);
lean_inc(v_cache_3086_);
lean_inc(v_mctx_3087_);
lean_dec(v___x_3085_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3115_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_inferType_3094_; lean_object* v_funInfo_3095_; lean_object* v_synthInstance_3096_; lean_object* v_whnf_3097_; lean_object* v_defEqTrans_3098_; lean_object* v_defEqPerm_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3114_; 
v_inferType_3094_ = lean_ctor_get(v_cache_3086_, 0);
v_funInfo_3095_ = lean_ctor_get(v_cache_3086_, 1);
v_synthInstance_3096_ = lean_ctor_get(v_cache_3086_, 2);
v_whnf_3097_ = lean_ctor_get(v_cache_3086_, 3);
v_defEqTrans_3098_ = lean_ctor_get(v_cache_3086_, 4);
v_defEqPerm_3099_ = lean_ctor_get(v_cache_3086_, 5);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_cache_3086_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3101_ = v_cache_3086_;
v_isShared_3102_ = v_isSharedCheck_3114_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_defEqPerm_3099_);
lean_inc(v_defEqTrans_3098_);
lean_inc(v_whnf_3097_);
lean_inc(v_synthInstance_3096_);
lean_inc(v_funInfo_3095_);
lean_inc(v_inferType_3094_);
lean_dec(v_cache_3086_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3114_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
lean_inc(v_a_3080_);
v___x_3103_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3094_, v_a_3071_, v_a_3080_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_funInfo_3095_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_synthInstance_3096_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_whnf_3097_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_defEqTrans_3098_);
lean_ctor_set(v_reuseFailAlloc_3113_, 5, v_defEqPerm_3099_);
v___x_3105_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3107_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v___x_3105_);
v___x_3107_ = v___x_3092_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_mctx_3087_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_zetaDeltaFVarIds_3088_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_postponed_3089_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_diag_3090_);
v___x_3107_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = lean_st_ref_set(v_a_2906_, v___x_3107_);
if (v_isShared_3084_ == 0)
{
v___x_3110_ = v___x_3083_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3080_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3080_);
lean_dec(v_a_3071_);
return v___x_3079_;
}
}
else
{
lean_dec(v_a_3071_);
return v___x_3079_;
}
}
else
{
lean_object* v_val_3118_; lean_object* v___x_3120_; 
lean_dec(v_a_3071_);
lean_dec_ref(v_e_2904_);
v_val_3118_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_val_3118_);
lean_dec_ref(v___x_3078_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v_val_3118_);
v___x_3120_ = v___x_3073_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_val_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_e_2904_);
v_a_3123_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3070_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3070_);
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
v___x_3131_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_3131_;
}
}
}
case 9:
{
lean_object* v_a_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_a_3132_ = lean_ctor_get(v_e_2904_, 0);
lean_inc_ref(v_a_3132_);
lean_dec_ref(v_e_2904_);
v___x_3133_ = l_Lean_Literal_type(v_a_3132_);
lean_dec_ref(v_a_3132_);
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
return v___x_3134_;
}
case 10:
{
lean_object* v_expr_3135_; 
v_expr_3135_ = lean_ctor_get(v_e_2904_, 1);
lean_inc_ref(v_expr_3135_);
lean_dec_ref(v_e_2904_);
v_e_2904_ = v_expr_3135_;
goto _start;
}
case 11:
{
uint8_t v_cacheInferType_3137_; 
v_cacheInferType_3137_ = lean_ctor_get_uint8(v_a_2905_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3137_ == 0)
{
lean_object* v_typeName_3138_; lean_object* v_idx_3139_; lean_object* v_struct_3140_; lean_object* v___x_3141_; 
v_typeName_3138_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_typeName_3138_);
v_idx_3139_ = lean_ctor_get(v_e_2904_, 1);
lean_inc(v_idx_3139_);
v_struct_3140_ = lean_ctor_get(v_e_2904_, 2);
lean_inc_ref(v_struct_3140_);
lean_dec_ref(v_e_2904_);
v___x_3141_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3138_, v_idx_3139_, v_struct_3140_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_3141_;
}
else
{
lean_object* v_typeName_3142_; lean_object* v_idx_3143_; lean_object* v_struct_3144_; uint8_t v___x_3145_; 
v_typeName_3142_ = lean_ctor_get(v_e_2904_, 0);
lean_inc(v_typeName_3142_);
v_idx_3143_ = lean_ctor_get(v_e_2904_, 1);
lean_inc(v_idx_3143_);
v_struct_3144_ = lean_ctor_get(v_e_2904_, 2);
lean_inc_ref(v_struct_3144_);
v___x_3145_ = l_Lean_Expr_hasMVar(v_e_2904_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2904_, v_a_2905_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3198_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3198_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3198_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v_cache_3152_; lean_object* v_inferType_3153_; lean_object* v___x_3154_; 
v___x_3151_ = lean_st_ref_get(v_a_2906_);
v_cache_3152_ = lean_ctor_get(v___x_3151_, 1);
lean_inc_ref(v_cache_3152_);
lean_dec(v___x_3151_);
v_inferType_3153_ = lean_ctor_get(v_cache_3152_, 0);
lean_inc_ref(v_inferType_3153_);
lean_dec_ref(v_cache_3152_);
v___x_3154_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3153_, v_a_3147_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v___x_3155_; 
lean_del_object(v___x_3149_);
v___x_3155_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3142_, v_idx_3143_, v_struct_3144_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; uint8_t v___x_3157_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
v___x_3157_ = l_Lean_Expr_hasMVar(v_a_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3192_; 
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v___x_3155_, 0);
lean_dec(v_unused_3193_);
v___x_3159_ = v___x_3155_;
v_isShared_3160_ = v_isSharedCheck_3192_;
goto v_resetjp_3158_;
}
else
{
lean_dec(v___x_3155_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3192_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v_cache_3162_; lean_object* v_mctx_3163_; lean_object* v_zetaDeltaFVarIds_3164_; lean_object* v_postponed_3165_; lean_object* v_diag_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3191_; 
v___x_3161_ = lean_st_ref_take(v_a_2906_);
v_cache_3162_ = lean_ctor_get(v___x_3161_, 1);
v_mctx_3163_ = lean_ctor_get(v___x_3161_, 0);
v_zetaDeltaFVarIds_3164_ = lean_ctor_get(v___x_3161_, 2);
v_postponed_3165_ = lean_ctor_get(v___x_3161_, 3);
v_diag_3166_ = lean_ctor_get(v___x_3161_, 4);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3168_ = v___x_3161_;
v_isShared_3169_ = v_isSharedCheck_3191_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_diag_3166_);
lean_inc(v_postponed_3165_);
lean_inc(v_zetaDeltaFVarIds_3164_);
lean_inc(v_cache_3162_);
lean_inc(v_mctx_3163_);
lean_dec(v___x_3161_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3191_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v_inferType_3170_; lean_object* v_funInfo_3171_; lean_object* v_synthInstance_3172_; lean_object* v_whnf_3173_; lean_object* v_defEqTrans_3174_; lean_object* v_defEqPerm_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3190_; 
v_inferType_3170_ = lean_ctor_get(v_cache_3162_, 0);
v_funInfo_3171_ = lean_ctor_get(v_cache_3162_, 1);
v_synthInstance_3172_ = lean_ctor_get(v_cache_3162_, 2);
v_whnf_3173_ = lean_ctor_get(v_cache_3162_, 3);
v_defEqTrans_3174_ = lean_ctor_get(v_cache_3162_, 4);
v_defEqPerm_3175_ = lean_ctor_get(v_cache_3162_, 5);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_cache_3162_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3177_ = v_cache_3162_;
v_isShared_3178_ = v_isSharedCheck_3190_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_defEqPerm_3175_);
lean_inc(v_defEqTrans_3174_);
lean_inc(v_whnf_3173_);
lean_inc(v_synthInstance_3172_);
lean_inc(v_funInfo_3171_);
lean_inc(v_inferType_3170_);
lean_dec(v_cache_3162_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3190_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_inc(v_a_3156_);
v___x_3179_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3170_, v_a_3147_, v_a_3156_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3179_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_funInfo_3171_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_synthInstance_3172_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_whnf_3173_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_defEqTrans_3174_);
lean_ctor_set(v_reuseFailAlloc_3189_, 5, v_defEqPerm_3175_);
v___x_3181_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3181_);
v___x_3183_ = v___x_3168_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_mctx_3163_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_zetaDeltaFVarIds_3164_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_postponed_3165_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_diag_3166_);
v___x_3183_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3184_ = lean_st_ref_set(v_a_2906_, v___x_3183_);
if (v_isShared_3160_ == 0)
{
v___x_3186_ = v___x_3159_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3156_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3156_);
lean_dec(v_a_3147_);
return v___x_3155_;
}
}
else
{
lean_dec(v_a_3147_);
return v___x_3155_;
}
}
else
{
lean_object* v_val_3194_; lean_object* v___x_3196_; 
lean_dec(v_a_3147_);
lean_dec_ref(v_struct_3144_);
lean_dec(v_idx_3143_);
lean_dec(v_typeName_3142_);
v_val_3194_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_val_3194_);
lean_dec_ref(v___x_3154_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v_val_3194_);
v___x_3196_ = v___x_3149_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_val_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v_struct_3144_);
lean_dec(v_idx_3143_);
lean_dec(v_typeName_3142_);
v_a_3199_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3146_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3146_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
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
else
{
lean_object* v___x_3207_; 
lean_dec_ref(v_e_2904_);
v___x_3207_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3142_, v_idx_3143_, v_struct_3144_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_3207_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3208_; 
v_cacheInferType_3208_ = lean_ctor_get_uint8(v_a_2905_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3208_ == 0)
{
lean_object* v___x_3209_; 
v___x_3209_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_3209_;
}
else
{
uint8_t v___x_3210_; 
v___x_3210_ = l_Lean_Expr_hasMVar(v_e_2904_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; 
lean_inc_ref(v_e_2904_);
v___x_3211_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2904_, v_a_2905_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3263_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3263_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3263_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; lean_object* v_cache_3217_; lean_object* v_inferType_3218_; lean_object* v___x_3219_; 
v___x_3216_ = lean_st_ref_get(v_a_2906_);
v_cache_3217_ = lean_ctor_get(v___x_3216_, 1);
lean_inc_ref(v_cache_3217_);
lean_dec(v___x_3216_);
v_inferType_3218_ = lean_ctor_get(v_cache_3217_, 0);
lean_inc_ref(v_inferType_3218_);
lean_dec_ref(v_cache_3217_);
v___x_3219_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3218_, v_a_3212_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3220_; 
lean_del_object(v___x_3214_);
v___x_3220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; uint8_t v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
v___x_3222_ = l_Lean_Expr_hasMVar(v_a_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3257_; 
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v___x_3220_, 0);
lean_dec(v_unused_3258_);
v___x_3224_ = v___x_3220_;
v_isShared_3225_ = v_isSharedCheck_3257_;
goto v_resetjp_3223_;
}
else
{
lean_dec(v___x_3220_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3257_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v_cache_3227_; lean_object* v_mctx_3228_; lean_object* v_zetaDeltaFVarIds_3229_; lean_object* v_postponed_3230_; lean_object* v_diag_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3256_; 
v___x_3226_ = lean_st_ref_take(v_a_2906_);
v_cache_3227_ = lean_ctor_get(v___x_3226_, 1);
v_mctx_3228_ = lean_ctor_get(v___x_3226_, 0);
v_zetaDeltaFVarIds_3229_ = lean_ctor_get(v___x_3226_, 2);
v_postponed_3230_ = lean_ctor_get(v___x_3226_, 3);
v_diag_3231_ = lean_ctor_get(v___x_3226_, 4);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3233_ = v___x_3226_;
v_isShared_3234_ = v_isSharedCheck_3256_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_diag_3231_);
lean_inc(v_postponed_3230_);
lean_inc(v_zetaDeltaFVarIds_3229_);
lean_inc(v_cache_3227_);
lean_inc(v_mctx_3228_);
lean_dec(v___x_3226_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3256_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_inferType_3235_; lean_object* v_funInfo_3236_; lean_object* v_synthInstance_3237_; lean_object* v_whnf_3238_; lean_object* v_defEqTrans_3239_; lean_object* v_defEqPerm_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3255_; 
v_inferType_3235_ = lean_ctor_get(v_cache_3227_, 0);
v_funInfo_3236_ = lean_ctor_get(v_cache_3227_, 1);
v_synthInstance_3237_ = lean_ctor_get(v_cache_3227_, 2);
v_whnf_3238_ = lean_ctor_get(v_cache_3227_, 3);
v_defEqTrans_3239_ = lean_ctor_get(v_cache_3227_, 4);
v_defEqPerm_3240_ = lean_ctor_get(v_cache_3227_, 5);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_cache_3227_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3242_ = v_cache_3227_;
v_isShared_3243_ = v_isSharedCheck_3255_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_defEqPerm_3240_);
lean_inc(v_defEqTrans_3239_);
lean_inc(v_whnf_3238_);
lean_inc(v_synthInstance_3237_);
lean_inc(v_funInfo_3236_);
lean_inc(v_inferType_3235_);
lean_dec(v_cache_3227_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3255_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_inc(v_a_3221_);
v___x_3244_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3235_, v_a_3212_, v_a_3221_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3246_ = v___x_3242_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_funInfo_3236_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v_synthInstance_3237_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v_whnf_3238_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v_defEqTrans_3239_);
lean_ctor_set(v_reuseFailAlloc_3254_, 5, v_defEqPerm_3240_);
v___x_3246_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3248_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3246_);
v___x_3248_ = v___x_3233_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_mctx_3228_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_zetaDeltaFVarIds_3229_);
lean_ctor_set(v_reuseFailAlloc_3253_, 3, v_postponed_3230_);
lean_ctor_set(v_reuseFailAlloc_3253_, 4, v_diag_3231_);
v___x_3248_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_st_ref_set(v_a_2906_, v___x_3248_);
if (v_isShared_3225_ == 0)
{
v___x_3251_ = v___x_3224_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3221_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3221_);
lean_dec(v_a_3212_);
return v___x_3220_;
}
}
else
{
lean_dec(v_a_3212_);
return v___x_3220_;
}
}
else
{
lean_object* v_val_3259_; lean_object* v___x_3261_; 
lean_dec(v_a_3212_);
lean_dec_ref(v_e_2904_);
v_val_3259_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_val_3259_);
lean_dec_ref(v___x_3219_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_val_3259_);
v___x_3261_ = v___x_3214_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_val_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_e_2904_);
v_a_3264_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3211_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3211_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
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
else
{
lean_object* v___x_3272_; 
v___x_3272_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_);
return v___x_3272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b2_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_3281_, v_x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b2_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b2_3284_, v_x_3285_, v_x_3286_);
lean_dec_ref(v_x_3286_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3289_, v_x_3290_, v_x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object* v_00_u03b2_3293_, lean_object* v_x_3294_, size_t v_x_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3294_, v_x_3295_, v_x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
size_t v_x_3132__boxed_3302_; lean_object* v_res_3303_; 
v_x_3132__boxed_3302_ = lean_unbox_usize(v_x_3300_);
lean_dec(v_x_3300_);
v_res_3303_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(v_00_u03b2_3298_, v_x_3299_, v_x_3132__boxed_3302_, v_x_3301_);
lean_dec_ref(v_x_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, size_t v_x_3306_, size_t v_x_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3305_, v_x_3306_, v_x_3307_, v_x_3308_, v_x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_){
_start:
{
size_t v_x_3143__boxed_3317_; size_t v_x_3144__boxed_3318_; lean_object* v_res_3319_; 
v_x_3143__boxed_3317_ = lean_unbox_usize(v_x_3313_);
lean_dec(v_x_3313_);
v_x_3144__boxed_3318_ = lean_unbox_usize(v_x_3314_);
lean_dec(v_x_3314_);
v_res_3319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(v_00_u03b2_3311_, v_x_3312_, v_x_3143__boxed_3317_, v_x_3144__boxed_3318_, v_x_3315_, v_x_3316_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_heq_3323_, lean_object* v_i_3324_, lean_object* v_k_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_3321_, v_vals_3322_, v_i_3324_, v_k_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_keys_3328_, lean_object* v_vals_3329_, lean_object* v_heq_3330_, lean_object* v_i_3331_, lean_object* v_k_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(v_00_u03b2_3327_, v_keys_3328_, v_vals_3329_, v_heq_3330_, v_i_3331_, v_k_3332_);
lean_dec_ref(v_k_3332_);
lean_dec_ref(v_vals_3329_);
lean_dec_ref(v_keys_3328_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3334_, lean_object* v_n_3335_, lean_object* v_k_3336_, lean_object* v_v_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v_n_3335_, v_k_3336_, v_v_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3339_, size_t v_depth_3340_, lean_object* v_keys_3341_, lean_object* v_vals_3342_, lean_object* v_heq_3343_, lean_object* v_i_3344_, lean_object* v_entries_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_3340_, v_keys_3341_, v_vals_3342_, v_i_3344_, v_entries_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3347_, lean_object* v_depth_3348_, lean_object* v_keys_3349_, lean_object* v_vals_3350_, lean_object* v_heq_3351_, lean_object* v_i_3352_, lean_object* v_entries_3353_){
_start:
{
size_t v_depth_boxed_3354_; lean_object* v_res_3355_; 
v_depth_boxed_3354_ = lean_unbox_usize(v_depth_3348_);
lean_dec(v_depth_3348_);
v_res_3355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(v_00_u03b2_3347_, v_depth_boxed_3354_, v_keys_3349_, v_vals_3350_, v_heq_3351_, v_i_3352_, v_entries_3353_);
lean_dec_ref(v_vals_3350_);
lean_dec_ref(v_keys_3349_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3356_, lean_object* v_x_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_, lean_object* v_x_3360_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3357_, v_x_3358_, v_x_3359_, v_x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = l_Lean_maxRecDepthErrorMessage;
v___x_3368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3370_ = l_Lean_MessageData_ofFormat(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3372_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3373_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v___x_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3377_, 0, v_ref_3374_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3382_, lean_object* v_ref_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3383_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3390_, lean_object* v_ref_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3390_, v_ref_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_fileName_3404_; lean_object* v_fileMap_3405_; lean_object* v_options_3406_; lean_object* v_currRecDepth_3407_; lean_object* v_maxRecDepth_3408_; lean_object* v_ref_3409_; lean_object* v_currNamespace_3410_; lean_object* v_openDecls_3411_; lean_object* v_initHeartbeats_3412_; lean_object* v_maxHeartbeats_3413_; lean_object* v_quotContext_3414_; lean_object* v_currMacroScope_3415_; uint8_t v_diag_3416_; lean_object* v_cancelTk_x3f_3417_; uint8_t v_suppressElabErrors_3418_; lean_object* v_inheritedTraceOptions_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3544_; 
v_fileName_3404_ = lean_ctor_get(v_a_3401_, 0);
v_fileMap_3405_ = lean_ctor_get(v_a_3401_, 1);
v_options_3406_ = lean_ctor_get(v_a_3401_, 2);
v_currRecDepth_3407_ = lean_ctor_get(v_a_3401_, 3);
v_maxRecDepth_3408_ = lean_ctor_get(v_a_3401_, 4);
v_ref_3409_ = lean_ctor_get(v_a_3401_, 5);
v_currNamespace_3410_ = lean_ctor_get(v_a_3401_, 6);
v_openDecls_3411_ = lean_ctor_get(v_a_3401_, 7);
v_initHeartbeats_3412_ = lean_ctor_get(v_a_3401_, 8);
v_maxHeartbeats_3413_ = lean_ctor_get(v_a_3401_, 9);
v_quotContext_3414_ = lean_ctor_get(v_a_3401_, 10);
v_currMacroScope_3415_ = lean_ctor_get(v_a_3401_, 11);
v_diag_3416_ = lean_ctor_get_uint8(v_a_3401_, sizeof(void*)*14);
v_cancelTk_x3f_3417_ = lean_ctor_get(v_a_3401_, 12);
v_suppressElabErrors_3418_ = lean_ctor_get_uint8(v_a_3401_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3419_ = lean_ctor_get(v_a_3401_, 13);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3401_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3421_ = v_a_3401_;
v_isShared_3422_ = v_isSharedCheck_3544_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_inheritedTraceOptions_3419_);
lean_inc(v_cancelTk_x3f_3417_);
lean_inc(v_currMacroScope_3415_);
lean_inc(v_quotContext_3414_);
lean_inc(v_maxHeartbeats_3413_);
lean_inc(v_initHeartbeats_3412_);
lean_inc(v_openDecls_3411_);
lean_inc(v_currNamespace_3410_);
lean_inc(v_ref_3409_);
lean_inc(v_maxRecDepth_3408_);
lean_inc(v_currRecDepth_3407_);
lean_inc(v_options_3406_);
lean_inc(v_fileMap_3405_);
lean_inc(v_fileName_3404_);
lean_dec(v_a_3401_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3544_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
uint8_t v___x_3423_; 
v___x_3423_ = lean_nat_dec_eq(v_currRecDepth_3407_, v_maxRecDepth_3408_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; uint8_t v_transparency_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3424_ = l_Lean_Meta_Context_config(v_a_3399_);
v_transparency_3425_ = lean_ctor_get_uint8(v___x_3424_, 9);
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_nat_add(v_currRecDepth_3407_, v___x_3426_);
lean_dec(v_currRecDepth_3407_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 3, v___x_3427_);
v___x_3429_ = v___x_3421_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_fileName_3404_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_fileMap_3405_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v_options_3406_);
lean_ctor_set(v_reuseFailAlloc_3542_, 3, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3542_, 4, v_maxRecDepth_3408_);
lean_ctor_set(v_reuseFailAlloc_3542_, 5, v_ref_3409_);
lean_ctor_set(v_reuseFailAlloc_3542_, 6, v_currNamespace_3410_);
lean_ctor_set(v_reuseFailAlloc_3542_, 7, v_openDecls_3411_);
lean_ctor_set(v_reuseFailAlloc_3542_, 8, v_initHeartbeats_3412_);
lean_ctor_set(v_reuseFailAlloc_3542_, 9, v_maxHeartbeats_3413_);
lean_ctor_set(v_reuseFailAlloc_3542_, 10, v_quotContext_3414_);
lean_ctor_set(v_reuseFailAlloc_3542_, 11, v_currMacroScope_3415_);
lean_ctor_set(v_reuseFailAlloc_3542_, 12, v_cancelTk_x3f_3417_);
lean_ctor_set(v_reuseFailAlloc_3542_, 13, v_inheritedTraceOptions_3419_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, sizeof(void*)*14, v_diag_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, sizeof(void*)*14 + 1, v_suppressElabErrors_3418_);
v___x_3429_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
uint8_t v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; uint8_t v___y_3436_; lean_object* v___y_3437_; uint8_t v___y_3438_; lean_object* v___y_3439_; uint8_t v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3470_; uint8_t v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = 1;
v___x_3541_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3425_, v___x_3540_);
if (v___x_3541_ == 0)
{
v___y_3470_ = v_transparency_3425_;
goto v___jp_3469_;
}
else
{
v___y_3470_ = v___x_3540_;
goto v___jp_3469_;
}
v___jp_3430_:
{
lean_object* v___x_3442_; uint8_t v_foApprox_3443_; uint8_t v_ctxApprox_3444_; uint8_t v_quasiPatternApprox_3445_; uint8_t v_constApprox_3446_; uint8_t v_isDefEqStuckEx_3447_; uint8_t v_unificationHints_3448_; uint8_t v_proofIrrelevance_3449_; uint8_t v_assignSyntheticOpaque_3450_; uint8_t v_offsetCnstrs_3451_; uint8_t v_transparency_3452_; uint8_t v_univApprox_3453_; uint8_t v_zetaUnused_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3468_; 
v___x_3442_ = l_Lean_Meta_Context_config(v___y_3437_);
lean_dec_ref(v___y_3437_);
v_foApprox_3443_ = lean_ctor_get_uint8(v___x_3442_, 0);
v_ctxApprox_3444_ = lean_ctor_get_uint8(v___x_3442_, 1);
v_quasiPatternApprox_3445_ = lean_ctor_get_uint8(v___x_3442_, 2);
v_constApprox_3446_ = lean_ctor_get_uint8(v___x_3442_, 3);
v_isDefEqStuckEx_3447_ = lean_ctor_get_uint8(v___x_3442_, 4);
v_unificationHints_3448_ = lean_ctor_get_uint8(v___x_3442_, 5);
v_proofIrrelevance_3449_ = lean_ctor_get_uint8(v___x_3442_, 6);
v_assignSyntheticOpaque_3450_ = lean_ctor_get_uint8(v___x_3442_, 7);
v_offsetCnstrs_3451_ = lean_ctor_get_uint8(v___x_3442_, 8);
v_transparency_3452_ = lean_ctor_get_uint8(v___x_3442_, 9);
v_univApprox_3453_ = lean_ctor_get_uint8(v___x_3442_, 11);
v_zetaUnused_3454_ = lean_ctor_get_uint8(v___x_3442_, 17);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3456_ = v___x_3442_;
v_isShared_3457_ = v_isSharedCheck_3468_;
goto v_resetjp_3455_;
}
else
{
lean_dec(v___x_3442_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3468_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
uint8_t v___x_3458_; uint8_t v___x_3459_; uint8_t v___x_3460_; lean_object* v___x_3462_; 
v___x_3458_ = 1;
v___x_3459_ = 0;
v___x_3460_ = 2;
if (v_isShared_3457_ == 0)
{
v___x_3462_ = v___x_3456_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 0, v_foApprox_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 1, v_ctxApprox_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 2, v_quasiPatternApprox_3445_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 3, v_constApprox_3446_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 4, v_isDefEqStuckEx_3447_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 5, v_unificationHints_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 6, v_proofIrrelevance_3449_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 7, v_assignSyntheticOpaque_3450_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 8, v_offsetCnstrs_3451_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 9, v_transparency_3452_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 11, v_univApprox_3453_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, 17, v_zetaUnused_3454_);
v___x_3462_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
uint64_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_ctor_set_uint8(v___x_3462_, 10, v___x_3459_);
lean_ctor_set_uint8(v___x_3462_, 12, v___x_3458_);
lean_ctor_set_uint8(v___x_3462_, 13, v___x_3458_);
lean_ctor_set_uint8(v___x_3462_, 14, v___x_3460_);
lean_ctor_set_uint8(v___x_3462_, 15, v___x_3458_);
lean_ctor_set_uint8(v___x_3462_, 16, v___x_3458_);
lean_ctor_set_uint8(v___x_3462_, 18, v___x_3458_);
v___x_3463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3462_);
v___x_3464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set_uint64(v___x_3464_, sizeof(void*)*1, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v___y_3432_);
lean_ctor_set(v___x_3465_, 2, v___y_3435_);
lean_ctor_set(v___x_3465_, 3, v___y_3439_);
lean_ctor_set(v___x_3465_, 4, v___y_3434_);
lean_ctor_set(v___x_3465_, 5, v___y_3441_);
lean_ctor_set(v___x_3465_, 6, v___y_3433_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*7, v___y_3436_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*7 + 1, v___y_3440_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*7 + 2, v___y_3431_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*7 + 3, v___y_3438_);
v___x_3466_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3398_, v___x_3465_, v_a_3400_, v___x_3429_, v_a_3402_);
lean_dec(v_a_3402_);
lean_dec_ref(v___x_3429_);
lean_dec(v_a_3400_);
lean_dec_ref(v___x_3465_);
return v___x_3466_;
}
}
}
v___jp_3469_:
{
uint8_t v_foApprox_3471_; uint8_t v_ctxApprox_3472_; uint8_t v_quasiPatternApprox_3473_; uint8_t v_constApprox_3474_; uint8_t v_isDefEqStuckEx_3475_; uint8_t v_unificationHints_3476_; uint8_t v_proofIrrelevance_3477_; uint8_t v_assignSyntheticOpaque_3478_; uint8_t v_offsetCnstrs_3479_; uint8_t v_etaStruct_3480_; uint8_t v_univApprox_3481_; uint8_t v_iota_3482_; uint8_t v_beta_3483_; uint8_t v_proj_3484_; uint8_t v_zeta_3485_; uint8_t v_zetaDelta_3486_; uint8_t v_zetaUnused_3487_; uint8_t v_zetaHave_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3539_; 
v_foApprox_3471_ = lean_ctor_get_uint8(v___x_3424_, 0);
v_ctxApprox_3472_ = lean_ctor_get_uint8(v___x_3424_, 1);
v_quasiPatternApprox_3473_ = lean_ctor_get_uint8(v___x_3424_, 2);
v_constApprox_3474_ = lean_ctor_get_uint8(v___x_3424_, 3);
v_isDefEqStuckEx_3475_ = lean_ctor_get_uint8(v___x_3424_, 4);
v_unificationHints_3476_ = lean_ctor_get_uint8(v___x_3424_, 5);
v_proofIrrelevance_3477_ = lean_ctor_get_uint8(v___x_3424_, 6);
v_assignSyntheticOpaque_3478_ = lean_ctor_get_uint8(v___x_3424_, 7);
v_offsetCnstrs_3479_ = lean_ctor_get_uint8(v___x_3424_, 8);
v_etaStruct_3480_ = lean_ctor_get_uint8(v___x_3424_, 10);
v_univApprox_3481_ = lean_ctor_get_uint8(v___x_3424_, 11);
v_iota_3482_ = lean_ctor_get_uint8(v___x_3424_, 12);
v_beta_3483_ = lean_ctor_get_uint8(v___x_3424_, 13);
v_proj_3484_ = lean_ctor_get_uint8(v___x_3424_, 14);
v_zeta_3485_ = lean_ctor_get_uint8(v___x_3424_, 15);
v_zetaDelta_3486_ = lean_ctor_get_uint8(v___x_3424_, 16);
v_zetaUnused_3487_ = lean_ctor_get_uint8(v___x_3424_, 17);
v_zetaHave_3488_ = lean_ctor_get_uint8(v___x_3424_, 18);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3490_ = v___x_3424_;
v_isShared_3491_ = v_isSharedCheck_3539_;
goto v_resetjp_3489_;
}
else
{
lean_dec(v___x_3424_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3539_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
uint8_t v_trackZetaDelta_3492_; lean_object* v_zetaDeltaSet_3493_; lean_object* v_lctx_3494_; lean_object* v_localInstances_3495_; lean_object* v_defEqCtx_x3f_3496_; lean_object* v_synthPendingDepth_3497_; lean_object* v_canUnfold_x3f_3498_; uint8_t v_univApprox_3499_; uint8_t v_inTypeClassResolution_3500_; uint8_t v_cacheInferType_3501_; lean_object* v_config_3503_; 
v_trackZetaDelta_3492_ = lean_ctor_get_uint8(v_a_3399_, sizeof(void*)*7);
v_zetaDeltaSet_3493_ = lean_ctor_get(v_a_3399_, 1);
lean_inc(v_zetaDeltaSet_3493_);
v_lctx_3494_ = lean_ctor_get(v_a_3399_, 2);
lean_inc_ref(v_lctx_3494_);
v_localInstances_3495_ = lean_ctor_get(v_a_3399_, 3);
lean_inc_ref(v_localInstances_3495_);
v_defEqCtx_x3f_3496_ = lean_ctor_get(v_a_3399_, 4);
lean_inc(v_defEqCtx_x3f_3496_);
v_synthPendingDepth_3497_ = lean_ctor_get(v_a_3399_, 5);
lean_inc(v_synthPendingDepth_3497_);
v_canUnfold_x3f_3498_ = lean_ctor_get(v_a_3399_, 6);
lean_inc(v_canUnfold_x3f_3498_);
v_univApprox_3499_ = lean_ctor_get_uint8(v_a_3399_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3500_ = lean_ctor_get_uint8(v_a_3399_, sizeof(void*)*7 + 2);
v_cacheInferType_3501_ = lean_ctor_get_uint8(v_a_3399_, sizeof(void*)*7 + 3);
if (v_isShared_3491_ == 0)
{
v_config_3503_ = v___x_3490_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 0, v_foApprox_3471_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 1, v_ctxApprox_3472_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 2, v_quasiPatternApprox_3473_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 3, v_constApprox_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 4, v_isDefEqStuckEx_3475_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 5, v_unificationHints_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 6, v_proofIrrelevance_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 7, v_assignSyntheticOpaque_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 8, v_offsetCnstrs_3479_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 10, v_etaStruct_3480_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 11, v_univApprox_3481_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 12, v_iota_3482_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 13, v_beta_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 14, v_proj_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 15, v_zeta_3485_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 16, v_zetaDelta_3486_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 17, v_zetaUnused_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3538_, 18, v_zetaHave_3488_);
v_config_3503_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
uint64_t v___x_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3530_; 
lean_ctor_set_uint8(v_config_3503_, 9, v___y_3470_);
v___x_3504_ = l_Lean_Meta_Context_configKey(v_a_3399_);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_a_3399_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; lean_object* v_unused_3532_; lean_object* v_unused_3533_; lean_object* v_unused_3534_; lean_object* v_unused_3535_; lean_object* v_unused_3536_; lean_object* v_unused_3537_; 
v_unused_3531_ = lean_ctor_get(v_a_3399_, 6);
lean_dec(v_unused_3531_);
v_unused_3532_ = lean_ctor_get(v_a_3399_, 5);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_a_3399_, 4);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_a_3399_, 3);
lean_dec(v_unused_3534_);
v_unused_3535_ = lean_ctor_get(v_a_3399_, 2);
lean_dec(v_unused_3535_);
v_unused_3536_ = lean_ctor_get(v_a_3399_, 1);
lean_dec(v_unused_3536_);
v_unused_3537_ = lean_ctor_get(v_a_3399_, 0);
lean_dec(v_unused_3537_);
v___x_3506_ = v_a_3399_;
v_isShared_3507_ = v_isSharedCheck_3530_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v_a_3399_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3530_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
uint64_t v___x_3508_; uint64_t v___x_3509_; uint64_t v___x_3510_; uint64_t v___x_3511_; uint64_t v_key_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3508_ = 2ULL;
v___x_3509_ = lean_uint64_shift_right(v___x_3504_, v___x_3508_);
v___x_3510_ = lean_uint64_shift_left(v___x_3509_, v___x_3508_);
v___x_3511_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3470_);
v_key_3512_ = lean_uint64_lor(v___x_3510_, v___x_3511_);
v___x_3513_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3513_, 0, v_config_3503_);
lean_ctor_set_uint64(v___x_3513_, sizeof(void*)*1, v_key_3512_);
lean_inc(v_canUnfold_x3f_3498_);
lean_inc(v_synthPendingDepth_3497_);
lean_inc(v_defEqCtx_x3f_3496_);
lean_inc_ref(v_localInstances_3495_);
lean_inc_ref(v_lctx_3494_);
lean_inc(v_zetaDeltaSet_3493_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3513_);
v___x_3515_ = v___x_3506_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_zetaDeltaSet_3493_);
lean_ctor_set(v_reuseFailAlloc_3529_, 2, v_lctx_3494_);
lean_ctor_set(v_reuseFailAlloc_3529_, 3, v_localInstances_3495_);
lean_ctor_set(v_reuseFailAlloc_3529_, 4, v_defEqCtx_x3f_3496_);
lean_ctor_set(v_reuseFailAlloc_3529_, 5, v_synthPendingDepth_3497_);
lean_ctor_set(v_reuseFailAlloc_3529_, 6, v_canUnfold_x3f_3498_);
lean_ctor_set_uint8(v_reuseFailAlloc_3529_, sizeof(void*)*7, v_trackZetaDelta_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3529_, sizeof(void*)*7 + 1, v_univApprox_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3529_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3500_);
lean_ctor_set_uint8(v_reuseFailAlloc_3529_, sizeof(void*)*7 + 3, v_cacheInferType_3501_);
v___x_3515_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3516_; uint8_t v_beta_3517_; 
v___x_3516_ = l_Lean_Meta_Context_config(v___x_3515_);
v_beta_3517_ = lean_ctor_get_uint8(v___x_3516_, 13);
if (v_beta_3517_ == 0)
{
lean_dec_ref(v___x_3516_);
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
uint8_t v_iota_3518_; 
v_iota_3518_ = lean_ctor_get_uint8(v___x_3516_, 12);
if (v_iota_3518_ == 0)
{
lean_dec_ref(v___x_3516_);
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
uint8_t v_zeta_3519_; 
v_zeta_3519_ = lean_ctor_get_uint8(v___x_3516_, 15);
if (v_zeta_3519_ == 0)
{
lean_dec_ref(v___x_3516_);
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
uint8_t v_zetaHave_3520_; 
v_zetaHave_3520_ = lean_ctor_get_uint8(v___x_3516_, 18);
if (v_zetaHave_3520_ == 0)
{
lean_dec_ref(v___x_3516_);
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
uint8_t v_zetaDelta_3521_; 
v_zetaDelta_3521_ = lean_ctor_get_uint8(v___x_3516_, 16);
if (v_zetaDelta_3521_ == 0)
{
lean_dec_ref(v___x_3516_);
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
uint8_t v_etaStruct_3522_; uint8_t v_proj_3523_; uint8_t v___x_3524_; uint8_t v___x_3525_; 
v_etaStruct_3522_ = lean_ctor_get_uint8(v___x_3516_, 10);
v_proj_3523_ = lean_ctor_get_uint8(v___x_3516_, 14);
lean_dec_ref(v___x_3516_);
v___x_3524_ = 2;
v___x_3525_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3523_, v___x_3524_);
if (v___x_3525_ == 0)
{
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
uint8_t v___x_3526_; uint8_t v___x_3527_; 
v___x_3526_ = 0;
v___x_3527_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3522_, v___x_3526_);
if (v___x_3527_ == 0)
{
v___y_3431_ = v_inTypeClassResolution_3500_;
v___y_3432_ = v_zetaDeltaSet_3493_;
v___y_3433_ = v_canUnfold_x3f_3498_;
v___y_3434_ = v_defEqCtx_x3f_3496_;
v___y_3435_ = v_lctx_3494_;
v___y_3436_ = v_trackZetaDelta_3492_;
v___y_3437_ = v___x_3515_;
v___y_3438_ = v_cacheInferType_3501_;
v___y_3439_ = v_localInstances_3495_;
v___y_3440_ = v_univApprox_3499_;
v___y_3441_ = v_synthPendingDepth_3497_;
goto v___jp_3430_;
}
else
{
lean_object* v___x_3528_; 
lean_dec(v_canUnfold_x3f_3498_);
lean_dec(v_synthPendingDepth_3497_);
lean_dec(v_defEqCtx_x3f_3496_);
lean_dec_ref(v_localInstances_3495_);
lean_dec_ref(v_lctx_3494_);
lean_dec(v_zetaDeltaSet_3493_);
v___x_3528_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3398_, v___x_3515_, v_a_3400_, v___x_3429_, v_a_3402_);
lean_dec(v_a_3402_);
lean_dec_ref(v___x_3429_);
lean_dec(v_a_3400_);
lean_dec_ref(v___x_3515_);
return v___x_3528_;
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
}
}
else
{
lean_object* v___x_3543_; 
lean_del_object(v___x_3421_);
lean_dec_ref(v_inheritedTraceOptions_3419_);
lean_dec(v_cancelTk_x3f_3417_);
lean_dec(v_currMacroScope_3415_);
lean_dec(v_quotContext_3414_);
lean_dec(v_maxHeartbeats_3413_);
lean_dec(v_initHeartbeats_3412_);
lean_dec(v_openDecls_3411_);
lean_dec(v_currNamespace_3410_);
lean_dec(v_maxRecDepth_3408_);
lean_dec(v_currRecDepth_3407_);
lean_dec_ref(v_options_3406_);
lean_dec_ref(v_fileMap_3405_);
lean_dec_ref(v_fileName_3404_);
lean_dec(v_a_3402_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec_ref(v_e_3398_);
v___x_3543_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3409_);
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = lean_infer_type(v_e_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v_res_3551_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3552_){
_start:
{
switch(lean_obj_tag(v_x_3552_))
{
case 0:
{
uint8_t v___x_3553_; 
v___x_3553_ = 1;
return v___x_3553_;
}
case 2:
{
lean_object* v_a_3554_; lean_object* v_a_3555_; uint8_t v___x_3556_; 
v_a_3554_ = lean_ctor_get(v_x_3552_, 0);
v_a_3555_ = lean_ctor_get(v_x_3552_, 1);
v___x_3556_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3554_);
if (v___x_3556_ == 0)
{
return v___x_3556_;
}
else
{
v_x_3552_ = v_a_3555_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3558_; 
v_a_3558_ = lean_ctor_get(v_x_3552_, 1);
v_x_3552_ = v_a_3558_;
goto _start;
}
default: 
{
uint8_t v___x_3560_; 
v___x_3560_ = 0;
return v___x_3560_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3561_){
_start:
{
uint8_t v_res_3562_; lean_object* v_r_3563_; 
v_res_3562_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3561_);
lean_dec(v_x_3561_);
v_r_3563_ = lean_box(v_res_3562_);
return v_r_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v___x_3567_; lean_object* v_mctx_3568_; lean_object* v___x_3569_; lean_object* v_fst_3570_; lean_object* v_snd_3571_; lean_object* v___x_3572_; lean_object* v_cache_3573_; lean_object* v_zetaDeltaFVarIds_3574_; lean_object* v_postponed_3575_; lean_object* v_diag_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3585_; 
v___x_3567_ = lean_st_ref_get(v___y_3565_);
v_mctx_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc_ref(v_mctx_3568_);
lean_dec(v___x_3567_);
v___x_3569_ = lean_instantiate_level_mvars(v_mctx_3568_, v_l_3564_);
v_fst_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_fst_3570_);
v_snd_3571_ = lean_ctor_get(v___x_3569_, 1);
lean_inc(v_snd_3571_);
lean_dec_ref(v___x_3569_);
v___x_3572_ = lean_st_ref_take(v___y_3565_);
v_cache_3573_ = lean_ctor_get(v___x_3572_, 1);
v_zetaDeltaFVarIds_3574_ = lean_ctor_get(v___x_3572_, 2);
v_postponed_3575_ = lean_ctor_get(v___x_3572_, 3);
v_diag_3576_ = lean_ctor_get(v___x_3572_, 4);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3586_);
v___x_3578_ = v___x_3572_;
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_diag_3576_);
lean_inc(v_postponed_3575_);
lean_inc(v_zetaDeltaFVarIds_3574_);
lean_inc(v_cache_3573_);
lean_dec(v___x_3572_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v_fst_3570_);
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_fst_3570_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_cache_3573_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_zetaDeltaFVarIds_3574_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v_postponed_3575_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_diag_3576_);
v___x_3581_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_st_ref_set(v___y_3565_, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v_snd_3571_);
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3587_, v___y_3588_);
lean_dec(v___y_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3591_, v___y_3593_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3605_, lean_object* v_x_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
switch(lean_obj_tag(v_x_3605_))
{
case 3:
{
lean_object* v_u_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v_u_3616_ = lean_ctor_get(v_x_3605_, 0);
lean_inc(v_u_3616_);
lean_dec_ref(v_x_3605_);
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3618_ = lean_nat_dec_eq(v_x_3606_, v___x_3617_);
lean_dec(v_x_3606_);
if (v___x_3618_ == 0)
{
lean_dec(v_u_3616_);
goto v___jp_3612_;
}
else
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3616_, v_a_3608_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3630_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3630_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3630_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
uint8_t v___x_3624_; uint8_t v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3624_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3620_);
lean_dec(v_a_3620_);
v___x_3625_ = l_Bool_toLBool(v___x_3624_);
v___x_3626_ = lean_box(v___x_3625_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 0, v___x_3626_);
v___x_3628_ = v___x_3622_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
v_a_3631_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3619_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3619_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3639_; lean_object* v_zero_3640_; uint8_t v_isZero_3641_; 
v_body_3639_ = lean_ctor_get(v_x_3605_, 2);
lean_inc_ref(v_body_3639_);
lean_dec_ref(v_x_3605_);
v_zero_3640_ = lean_unsigned_to_nat(0u);
v_isZero_3641_ = lean_nat_dec_eq(v_x_3606_, v_zero_3640_);
if (v_isZero_3641_ == 1)
{
uint8_t v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec_ref(v_body_3639_);
lean_dec(v_x_3606_);
v___x_3642_ = 0;
v___x_3643_ = lean_box(v___x_3642_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
else
{
lean_object* v_one_3645_; lean_object* v_n_3646_; 
v_one_3645_ = lean_unsigned_to_nat(1u);
v_n_3646_ = lean_nat_sub(v_x_3606_, v_one_3645_);
lean_dec(v_x_3606_);
v_x_3605_ = v_body_3639_;
v_x_3606_ = v_n_3646_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3648_; 
v_body_3648_ = lean_ctor_get(v_x_3605_, 3);
lean_inc_ref(v_body_3648_);
lean_dec_ref(v_x_3605_);
v_x_3605_ = v_body_3648_;
goto _start;
}
case 10:
{
lean_object* v_expr_3650_; 
v_expr_3650_ = lean_ctor_get(v_x_3605_, 1);
lean_inc_ref(v_expr_3650_);
lean_dec_ref(v_x_3605_);
v_x_3605_ = v_expr_3650_;
goto _start;
}
default: 
{
lean_dec(v_x_3606_);
lean_dec_ref(v_x_3605_);
goto v___jp_3612_;
}
}
v___jp_3612_:
{
uint8_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3613_ = 2;
v___x_3614_ = lean_box(v___x_3613_);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3652_, lean_object* v_x_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3652_, v_x_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
lean_dec(v_a_3657_);
lean_dec_ref(v_a_3656_);
lean_dec(v_a_3655_);
lean_dec_ref(v_a_3654_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3660_, lean_object* v_x_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
switch(lean_obj_tag(v_x_3660_))
{
case 4:
{
lean_object* v_declName_3667_; lean_object* v_us_3668_; lean_object* v___x_3669_; 
v_declName_3667_ = lean_ctor_get(v_x_3660_, 0);
lean_inc(v_declName_3667_);
v_us_3668_ = lean_ctor_get(v_x_3660_, 1);
lean_inc(v_us_3668_);
lean_dec_ref(v_x_3660_);
v___x_3669_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3667_, v_us_3668_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v___x_3671_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3670_, v_x_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
return v___x_3671_;
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_x_3661_);
v_a_3672_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3669_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3669_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3680_; lean_object* v___x_3681_; 
v_fvarId_3680_ = lean_ctor_get(v_x_3660_, 0);
lean_inc(v_fvarId_3680_);
lean_dec_ref(v_x_3660_);
v___x_3681_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3680_, v_a_3662_, v_a_3664_, v_a_3665_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
v___x_3683_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3682_, v_x_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
return v___x_3683_;
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v_x_3661_);
v_a_3684_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3681_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3681_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3692_; lean_object* v___x_3693_; 
v_mvarId_3692_ = lean_ctor_get(v_x_3660_, 0);
lean_inc(v_mvarId_3692_);
lean_dec_ref(v_x_3660_);
v___x_3693_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3692_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3695_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref(v___x_3693_);
v___x_3695_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3694_, v_x_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
return v___x_3695_;
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_x_3661_);
v_a_3696_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3693_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3693_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
case 5:
{
lean_object* v_fn_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_fn_3704_ = lean_ctor_get(v_x_3660_, 0);
lean_inc_ref(v_fn_3704_);
lean_dec_ref(v_x_3660_);
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_nat_add(v_x_3661_, v___x_3705_);
lean_dec(v_x_3661_);
v_x_3660_ = v_fn_3704_;
v_x_3661_ = v___x_3706_;
goto _start;
}
case 10:
{
lean_object* v_expr_3708_; 
v_expr_3708_ = lean_ctor_get(v_x_3660_, 1);
lean_inc_ref(v_expr_3708_);
lean_dec_ref(v_x_3660_);
v_x_3660_ = v_expr_3708_;
goto _start;
}
case 8:
{
lean_object* v_body_3710_; 
v_body_3710_ = lean_ctor_get(v_x_3660_, 3);
lean_inc_ref(v_body_3710_);
lean_dec_ref(v_x_3660_);
v_x_3660_ = v_body_3710_;
goto _start;
}
case 6:
{
lean_object* v_body_3712_; lean_object* v_zero_3713_; uint8_t v_isZero_3714_; 
v_body_3712_ = lean_ctor_get(v_x_3660_, 2);
lean_inc_ref(v_body_3712_);
lean_dec_ref(v_x_3660_);
v_zero_3713_ = lean_unsigned_to_nat(0u);
v_isZero_3714_ = lean_nat_dec_eq(v_x_3661_, v_zero_3713_);
if (v_isZero_3714_ == 1)
{
uint8_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec_ref(v_body_3712_);
lean_dec(v_x_3661_);
v___x_3715_ = 0;
v___x_3716_ = lean_box(v___x_3715_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
else
{
lean_object* v_one_3718_; lean_object* v_n_3719_; 
v_one_3718_ = lean_unsigned_to_nat(1u);
v_n_3719_ = lean_nat_sub(v_x_3661_, v_one_3718_);
lean_dec(v_x_3661_);
v_x_3660_ = v_body_3712_;
v_x_3661_ = v_n_3719_;
goto _start;
}
}
default: 
{
uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec(v_x_3661_);
lean_dec_ref(v_x_3660_);
v___x_3721_ = 2;
v___x_3722_ = lean_box(v___x_3721_);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3724_, lean_object* v_x_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3724_, v_x_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
switch(lean_obj_tag(v_x_3732_))
{
case 0:
{
uint8_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec_ref(v_x_3732_);
v___x_3738_ = 2;
v___x_3739_ = lean_box(v___x_3738_);
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
case 1:
{
lean_object* v_fvarId_3741_; lean_object* v___x_3742_; 
v_fvarId_3741_ = lean_ctor_get(v_x_3732_, 0);
lean_inc(v_fvarId_3741_);
lean_dec_ref(v_x_3732_);
v___x_3742_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3741_, v_a_3733_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref(v___x_3742_);
v___x_3744_ = lean_unsigned_to_nat(0u);
v___x_3745_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3743_, v___x_3744_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3745_;
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_a_3746_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3742_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3742_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3754_; lean_object* v___x_3755_; 
v_mvarId_3754_ = lean_ctor_get(v_x_3732_, 0);
lean_inc(v_mvarId_3754_);
lean_dec_ref(v_x_3732_);
v___x_3755_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3754_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___x_3755_);
v___x_3757_ = lean_unsigned_to_nat(0u);
v___x_3758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3756_, v___x_3757_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3758_;
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
v_a_3759_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3755_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3755_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
case 4:
{
lean_object* v_declName_3767_; lean_object* v_us_3768_; lean_object* v___x_3769_; 
v_declName_3767_ = lean_ctor_get(v_x_3732_, 0);
lean_inc(v_declName_3767_);
v_us_3768_ = lean_ctor_get(v_x_3732_, 1);
lean_inc(v_us_3768_);
lean_dec_ref(v_x_3732_);
v___x_3769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3767_, v_us_3768_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(0u);
v___x_3772_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3770_, v___x_3771_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3772_;
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
v_a_3773_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3769_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3769_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
case 5:
{
lean_object* v_fn_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_fn_3781_ = lean_ctor_get(v_x_3732_, 0);
lean_inc_ref(v_fn_3781_);
lean_dec_ref(v_x_3732_);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_3781_, v___x_3782_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3783_;
}
case 7:
{
lean_object* v_body_3784_; 
v_body_3784_ = lean_ctor_get(v_x_3732_, 2);
lean_inc_ref(v_body_3784_);
lean_dec_ref(v_x_3732_);
v_x_3732_ = v_body_3784_;
goto _start;
}
case 8:
{
lean_object* v_body_3786_; 
v_body_3786_ = lean_ctor_get(v_x_3732_, 3);
lean_inc_ref(v_body_3786_);
lean_dec_ref(v_x_3732_);
v_x_3732_ = v_body_3786_;
goto _start;
}
case 10:
{
lean_object* v_expr_3788_; 
v_expr_3788_ = lean_ctor_get(v_x_3732_, 1);
lean_inc_ref(v_expr_3788_);
lean_dec_ref(v_x_3732_);
v_x_3732_ = v_expr_3788_;
goto _start;
}
case 11:
{
uint8_t v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v_x_3732_);
v___x_3790_ = 2;
v___x_3791_ = lean_box(v___x_3790_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
default: 
{
uint8_t v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_dec_ref(v_x_3732_);
v___x_3793_ = 0;
v___x_3794_ = lean_box(v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
return v___x_3795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Meta_isPropQuick(v_x_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___x_3809_; 
lean_inc_ref(v_e_3803_);
v___x_3809_ = l_Lean_Meta_isPropQuick(v_e_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3866_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3866_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3866_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_unbox(v_a_3810_);
lean_dec(v_a_3810_);
switch(v___x_3814_)
{
case 0:
{
uint8_t v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_dec_ref(v_e_3803_);
v___x_3815_ = 0;
v___x_3816_ = lean_box(v___x_3815_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3816_);
v___x_3818_ = v___x_3812_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
case 1:
{
uint8_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_dec_ref(v_e_3803_);
v___x_3820_ = 1;
v___x_3821_ = lean_box(v___x_3820_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3821_);
v___x_3823_ = v___x_3812_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
default: 
{
lean_object* v___x_3825_; 
lean_del_object(v___x_3812_);
lean_inc(v_a_3807_);
lean_inc_ref(v_a_3806_);
lean_inc(v_a_3805_);
lean_inc_ref(v_a_3804_);
v___x_3825_ = lean_infer_type(v_e_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3827_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = l_Lean_Meta_whnfD(v_a_3826_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3849_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3849_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3849_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
if (lean_obj_tag(v_a_3828_) == 3)
{
lean_object* v_u_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3843_; 
lean_del_object(v___x_3830_);
v_u_3832_ = lean_ctor_get(v_a_3828_, 0);
lean_inc(v_u_3832_);
lean_dec_ref(v_a_3828_);
v___x_3833_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3832_, v_a_3805_);
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3843_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3843_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3838_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3834_);
lean_dec(v_a_3834_);
v___x_3839_ = lean_box(v___x_3838_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3839_);
v___x_3841_ = v___x_3836_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
else
{
uint8_t v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
lean_dec(v_a_3828_);
v___x_3844_ = 0;
v___x_3845_ = lean_box(v___x_3844_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3845_);
v___x_3847_ = v___x_3830_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
v_a_3850_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3827_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3827_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
v_a_3858_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3825_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3825_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec_ref(v_e_3803_);
v_a_3867_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3809_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3809_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_Meta_isProp(v_e_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
lean_dec(v_a_3879_);
lean_dec_ref(v_a_3878_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_3882_){
_start:
{
switch(lean_obj_tag(v_x_3882_))
{
case 0:
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_unsigned_to_nat(0u);
return v___x_3883_;
}
case 1:
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_unsigned_to_nat(1u);
return v___x_3884_;
}
case 2:
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_unsigned_to_nat(2u);
return v___x_3885_;
}
default: 
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_unsigned_to_nat(3u);
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_3887_);
lean_dec(v_x_3887_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_3889_, lean_object* v_k_3890_){
_start:
{
if (lean_obj_tag(v_t_3889_) == 3)
{
lean_object* v_idx_3891_; lean_object* v___x_3892_; 
v_idx_3891_ = lean_ctor_get(v_t_3889_, 0);
lean_inc(v_idx_3891_);
lean_dec_ref(v_t_3889_);
v___x_3892_ = lean_apply_1(v_k_3890_, v_idx_3891_);
return v___x_3892_;
}
else
{
lean_dec(v_t_3889_);
return v_k_3890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_3893_, lean_object* v_ctorIdx_3894_, lean_object* v_t_3895_, lean_object* v_h_3896_, lean_object* v_k_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3895_, v_k_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_3899_, lean_object* v_ctorIdx_3900_, lean_object* v_t_3901_, lean_object* v_h_3902_, lean_object* v_k_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_3899_, v_ctorIdx_3900_, v_t_3901_, v_h_3902_, v_k_3903_);
lean_dec(v_ctorIdx_3900_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_3905_, lean_object* v_false_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3905_, v_false_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_3908_, lean_object* v_t_3909_, lean_object* v_h_3910_, lean_object* v_false_3911_){
_start:
{
lean_object* v___x_3912_; 
v___x_3912_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3909_, v_false_3911_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_3913_, lean_object* v_true_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3913_, v_true_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_3916_, lean_object* v_t_3917_, lean_object* v_h_3918_, lean_object* v_true_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3917_, v_true_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_3921_, lean_object* v_undef_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3921_, v_undef_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_3924_, lean_object* v_t_3925_, lean_object* v_h_3926_, lean_object* v_undef_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3925_, v_undef_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_3929_, lean_object* v_bvar_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3929_, v_bvar_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_3932_, lean_object* v_t_3933_, lean_object* v_h_3934_, lean_object* v_bvar_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3933_, v_bvar_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_3937_){
_start:
{
switch(v_x_3937_)
{
case 0:
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_box(0);
return v___x_3938_;
}
case 1:
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_box(1);
return v___x_3939_;
}
default: 
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_box(2);
return v___x_3940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_3941_){
_start:
{
uint8_t v_x_25__boxed_3942_; lean_object* v_res_3943_; 
v_x_25__boxed_3942_ = lean_unbox(v_x_3941_);
v_res_3943_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_3942_);
return v_res_3943_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_3944_){
_start:
{
switch(lean_obj_tag(v_x_3944_))
{
case 0:
{
uint8_t v___x_3945_; 
v___x_3945_ = 0;
return v___x_3945_;
}
case 1:
{
uint8_t v___x_3946_; 
v___x_3946_ = 1;
return v___x_3946_;
}
default: 
{
uint8_t v___x_3947_; 
v___x_3947_ = 2;
return v___x_3947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_3948_){
_start:
{
uint8_t v_res_3949_; lean_object* v_r_3950_; 
v_res_3949_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_3948_);
lean_dec(v_x_3948_);
v_r_3950_ = lean_box(v_res_3949_);
return v_r_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_3952_){
_start:
{
switch(lean_obj_tag(v_e_3952_))
{
case 3:
{
lean_object* v_u_3953_; uint8_t v___x_3954_; 
v_u_3953_ = lean_ctor_get(v_e_3952_, 0);
v___x_3954_ = l_Lean_Level_isNeverZero(v_u_3953_);
if (v___x_3954_ == 0)
{
uint8_t v___x_3955_; 
v___x_3955_ = l_Lean_Level_isZero(v_u_3953_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_box(2);
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_box(1);
return v___x_3957_;
}
}
else
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_box(0);
return v___x_3958_;
}
}
case 5:
{
lean_object* v_fn_3959_; 
v_fn_3959_ = lean_ctor_get(v_e_3952_, 0);
if (lean_obj_tag(v_fn_3959_) == 4)
{
lean_object* v_declName_3960_; 
v_declName_3960_ = lean_ctor_get(v_fn_3959_, 0);
if (lean_obj_tag(v_declName_3960_) == 1)
{
lean_object* v_pre_3961_; 
v_pre_3961_ = lean_ctor_get(v_declName_3960_, 0);
if (lean_obj_tag(v_pre_3961_) == 0)
{
lean_object* v_arg_3962_; lean_object* v_str_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; 
v_arg_3962_ = lean_ctor_get(v_e_3952_, 1);
v_str_3963_ = lean_ctor_get(v_declName_3960_, 1);
v___x_3964_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_3965_ = lean_string_dec_eq(v_str_3963_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_box(2);
return v___x_3966_;
}
else
{
v_e_3952_ = v_arg_3962_;
goto _start;
}
}
else
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_box(2);
return v___x_3968_;
}
}
else
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_box(2);
return v___x_3969_;
}
}
else
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_box(2);
return v___x_3970_;
}
}
default: 
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_box(2);
return v___x_3971_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_3972_);
lean_dec_ref(v_e_3972_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_3974_, lean_object* v_binderType_3975_){
_start:
{
if (lean_obj_tag(v_r_3974_) == 3)
{
lean_object* v_idx_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3988_; 
v_idx_3976_ = lean_ctor_get(v_r_3974_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_r_3974_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3978_ = v_r_3974_;
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_idx_3976_);
lean_dec(v_r_3974_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_zero_3980_; uint8_t v_isZero_3981_; 
v_zero_3980_ = lean_unsigned_to_nat(0u);
v_isZero_3981_ = lean_nat_dec_eq(v_idx_3976_, v_zero_3980_);
if (v_isZero_3981_ == 1)
{
lean_object* v___x_3982_; 
lean_del_object(v___x_3978_);
lean_dec(v_idx_3976_);
v___x_3982_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_3975_);
return v___x_3982_;
}
else
{
lean_object* v_one_3983_; lean_object* v_n_3984_; lean_object* v___x_3986_; 
v_one_3983_ = lean_unsigned_to_nat(1u);
v_n_3984_ = lean_nat_sub(v_idx_3976_, v_one_3983_);
lean_dec(v_idx_3976_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v_n_3984_);
v___x_3986_ = v___x_3978_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_n_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
return v_r_3974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_3989_, lean_object* v_binderType_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_3989_, v_binderType_3990_);
lean_dec_ref(v_binderType_3990_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_3992_, lean_object* v_x_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_type_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; 
switch(lean_obj_tag(v_x_3992_))
{
case 7:
{
lean_object* v_binderType_4027_; lean_object* v_body_4028_; lean_object* v_zero_4029_; uint8_t v_isZero_4030_; 
v_binderType_4027_ = lean_ctor_get(v_x_3992_, 1);
v_body_4028_ = lean_ctor_get(v_x_3992_, 2);
v_zero_4029_ = lean_unsigned_to_nat(0u);
v_isZero_4030_ = lean_nat_dec_eq(v_x_3993_, v_zero_4029_);
if (v_isZero_4030_ == 1)
{
v_type_4000_ = v_x_3992_;
v___y_4001_ = v_a_3994_;
v___y_4002_ = v_a_3995_;
v___y_4003_ = v_a_3996_;
v___y_4004_ = v_a_3997_;
goto v___jp_3999_;
}
else
{
lean_object* v_one_4031_; lean_object* v_n_4032_; lean_object* v___x_4033_; 
lean_inc_ref(v_body_4028_);
lean_inc_ref(v_binderType_4027_);
lean_dec_ref(v_x_3992_);
v_one_4031_ = lean_unsigned_to_nat(1u);
v_n_4032_ = lean_nat_sub(v_x_3993_, v_one_4031_);
v___x_4033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4028_, v_n_4032_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
lean_dec(v_n_4032_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4042_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4042_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4042_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4038_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4034_, v_binderType_4027_);
lean_dec_ref(v_binderType_4027_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v___x_4038_);
v___x_4040_ = v___x_4036_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
else
{
lean_dec_ref(v_binderType_4027_);
return v___x_4033_;
}
}
}
case 8:
{
lean_object* v_type_4043_; lean_object* v_body_4044_; lean_object* v___x_4045_; 
v_type_4043_ = lean_ctor_get(v_x_3992_, 1);
lean_inc_ref(v_type_4043_);
v_body_4044_ = lean_ctor_get(v_x_3992_, 3);
lean_inc_ref(v_body_4044_);
lean_dec_ref(v_x_3992_);
v___x_4045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4044_, v_x_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4054_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4054_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4045_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4054_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4050_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4046_, v_type_4043_);
lean_dec_ref(v_type_4043_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4050_);
v___x_4052_ = v___x_4048_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_dec_ref(v_type_4043_);
return v___x_4045_;
}
}
case 10:
{
lean_object* v_expr_4055_; 
v_expr_4055_ = lean_ctor_get(v_x_3992_, 1);
lean_inc_ref(v_expr_4055_);
lean_dec_ref(v_x_3992_);
v_x_3992_ = v_expr_4055_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v_deBruijnIndex_4057_ = lean_ctor_get(v_x_3992_, 0);
lean_inc(v_deBruijnIndex_4057_);
lean_dec_ref(v_x_3992_);
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = lean_nat_dec_eq(v_x_3993_, v___x_4058_);
if (v___x_4059_ == 0)
{
lean_dec(v_deBruijnIndex_4057_);
goto v___jp_4024_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_deBruijnIndex_4057_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
return v___x_4061_;
}
}
default: 
{
lean_object* v___x_4062_; uint8_t v___x_4063_; 
v___x_4062_ = lean_unsigned_to_nat(0u);
v___x_4063_ = lean_nat_dec_eq(v_x_3993_, v___x_4062_);
if (v___x_4063_ == 0)
{
lean_dec_ref(v_x_3992_);
goto v___jp_4024_;
}
else
{
v_type_4000_ = v_x_3992_;
v___y_4001_ = v_a_3994_;
v___y_4002_ = v_a_3995_;
v___y_4003_ = v_a_3996_;
v___y_4004_ = v_a_3997_;
goto v___jp_3999_;
}
}
}
v___jp_3999_:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_Meta_isPropQuick(v_type_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4015_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4015_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4015_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4010_ = lean_unbox(v_a_4006_);
lean_dec(v_a_4006_);
v___x_4011_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4010_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4011_);
v___x_4013_ = v___x_4008_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
v_a_4016_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4005_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4005_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
v___jp_4024_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_box(2);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4064_, lean_object* v_x_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4064_, v_x_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_x_4065_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4072_, lean_object* v_n_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4072_, v_n_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4089_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4080_);
lean_dec(v_a_4080_);
v___x_4085_ = lean_box(v___x_4084_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4085_);
v___x_4087_ = v___x_4082_;
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
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
v_a_4090_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4079_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4079_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4098_, lean_object* v_n_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4098_, v_n_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_n_4099_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4106_, lean_object* v_x_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
switch(lean_obj_tag(v_x_4106_))
{
case 4:
{
lean_object* v_declName_4113_; lean_object* v_us_4114_; lean_object* v___x_4115_; 
v_declName_4113_ = lean_ctor_get(v_x_4106_, 0);
lean_inc(v_declName_4113_);
v_us_4114_ = lean_ctor_get(v_x_4106_, 1);
lean_inc(v_us_4114_);
lean_dec_ref(v_x_4106_);
v___x_4115_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4113_, v_us_4114_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4117_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4116_, v_x_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
lean_dec(v_x_4107_);
return v___x_4117_;
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_x_4107_);
v_a_4118_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4115_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4115_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4126_; lean_object* v___x_4127_; 
v_fvarId_4126_ = lean_ctor_get(v_x_4106_, 0);
lean_inc(v_fvarId_4126_);
lean_dec_ref(v_x_4106_);
v___x_4127_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4126_, v_a_4108_, v_a_4110_, v_a_4111_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref(v___x_4127_);
v___x_4129_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4128_, v_x_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
lean_dec(v_x_4107_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v_x_4107_);
v_a_4130_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4127_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4127_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4138_; lean_object* v___x_4139_; 
v_mvarId_4138_ = lean_ctor_get(v_x_4106_, 0);
lean_inc(v_mvarId_4138_);
lean_dec_ref(v_x_4106_);
v___x_4139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4138_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4141_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref(v___x_4139_);
v___x_4141_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4140_, v_x_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
lean_dec(v_x_4107_);
return v___x_4141_;
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_x_4107_);
v_a_4142_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4139_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4139_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
case 5:
{
lean_object* v_fn_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_fn_4150_ = lean_ctor_get(v_x_4106_, 0);
lean_inc_ref(v_fn_4150_);
lean_dec_ref(v_x_4106_);
v___x_4151_ = lean_unsigned_to_nat(1u);
v___x_4152_ = lean_nat_add(v_x_4107_, v___x_4151_);
lean_dec(v_x_4107_);
v_x_4106_ = v_fn_4150_;
v_x_4107_ = v___x_4152_;
goto _start;
}
case 10:
{
lean_object* v_expr_4154_; 
v_expr_4154_ = lean_ctor_get(v_x_4106_, 1);
lean_inc_ref(v_expr_4154_);
lean_dec_ref(v_x_4106_);
v_x_4106_ = v_expr_4154_;
goto _start;
}
case 8:
{
lean_object* v_body_4156_; 
v_body_4156_ = lean_ctor_get(v_x_4106_, 3);
lean_inc_ref(v_body_4156_);
lean_dec_ref(v_x_4106_);
v_x_4106_ = v_body_4156_;
goto _start;
}
case 6:
{
lean_object* v_body_4158_; lean_object* v_zero_4159_; uint8_t v_isZero_4160_; 
v_body_4158_ = lean_ctor_get(v_x_4106_, 2);
lean_inc_ref(v_body_4158_);
lean_dec_ref(v_x_4106_);
v_zero_4159_ = lean_unsigned_to_nat(0u);
v_isZero_4160_ = lean_nat_dec_eq(v_x_4107_, v_zero_4159_);
if (v_isZero_4160_ == 1)
{
lean_object* v___x_4161_; 
lean_dec(v_x_4107_);
v___x_4161_ = l_Lean_Meta_isProofQuick(v_body_4158_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
return v___x_4161_;
}
else
{
lean_object* v_one_4162_; lean_object* v_n_4163_; 
v_one_4162_ = lean_unsigned_to_nat(1u);
v_n_4163_ = lean_nat_sub(v_x_4107_, v_one_4162_);
lean_dec(v_x_4107_);
v_x_4106_ = v_body_4158_;
v_x_4107_ = v_n_4163_;
goto _start;
}
}
default: 
{
uint8_t v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_dec(v_x_4107_);
lean_dec_ref(v_x_4106_);
v___x_4165_ = 2;
v___x_4166_ = lean_box(v___x_4165_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
switch(lean_obj_tag(v_x_4168_))
{
case 0:
{
uint8_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec_ref(v_x_4168_);
v___x_4174_ = 2;
v___x_4175_ = lean_box(v___x_4174_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
case 1:
{
lean_object* v_fvarId_4177_; lean_object* v___x_4178_; 
v_fvarId_4177_ = lean_ctor_get(v_x_4168_, 0);
lean_inc(v_fvarId_4177_);
lean_dec_ref(v_x_4168_);
v___x_4178_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4177_, v_a_4169_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref(v___x_4178_);
v___x_4180_ = lean_unsigned_to_nat(0u);
v___x_4181_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4179_, v___x_4180_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
return v___x_4181_;
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4178_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4178_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4190_; lean_object* v___x_4191_; 
v_mvarId_4190_ = lean_ctor_get(v_x_4168_, 0);
lean_inc(v_mvarId_4190_);
lean_dec_ref(v_x_4168_);
v___x_4191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4190_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4192_, v___x_4193_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
return v___x_4194_;
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
v_a_4195_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4191_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4191_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
case 4:
{
lean_object* v_declName_4203_; lean_object* v_us_4204_; lean_object* v___x_4205_; 
v_declName_4203_ = lean_ctor_get(v_x_4168_, 0);
lean_inc(v_declName_4203_);
v_us_4204_ = lean_ctor_get(v_x_4168_, 1);
lean_inc(v_us_4204_);
lean_dec_ref(v_x_4168_);
v___x_4205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4203_, v_us_4204_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
v___x_4207_ = lean_unsigned_to_nat(0u);
v___x_4208_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4206_, v___x_4207_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
return v___x_4208_;
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
v_a_4209_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4205_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4205_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
case 5:
{
lean_object* v_fn_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_fn_4217_ = lean_ctor_get(v_x_4168_, 0);
lean_inc_ref(v_fn_4217_);
lean_dec_ref(v_x_4168_);
v___x_4218_ = lean_unsigned_to_nat(1u);
v___x_4219_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4217_, v___x_4218_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
return v___x_4219_;
}
case 6:
{
lean_object* v_body_4220_; 
v_body_4220_ = lean_ctor_get(v_x_4168_, 2);
lean_inc_ref(v_body_4220_);
lean_dec_ref(v_x_4168_);
v_x_4168_ = v_body_4220_;
goto _start;
}
case 8:
{
lean_object* v_body_4222_; 
v_body_4222_ = lean_ctor_get(v_x_4168_, 3);
lean_inc_ref(v_body_4222_);
lean_dec_ref(v_x_4168_);
v_x_4168_ = v_body_4222_;
goto _start;
}
case 10:
{
lean_object* v_expr_4224_; 
v_expr_4224_ = lean_ctor_get(v_x_4168_, 1);
lean_inc_ref(v_expr_4224_);
lean_dec_ref(v_x_4168_);
v_x_4168_ = v_expr_4224_;
goto _start;
}
case 11:
{
uint8_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_dec_ref(v_x_4168_);
v___x_4226_ = 2;
v___x_4227_ = lean_box(v___x_4226_);
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
default: 
{
uint8_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec_ref(v_x_4168_);
v___x_4229_ = 0;
v___x_4230_ = lean_box(v___x_4229_);
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
return v___x_4231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Meta_isProofQuick(v_x_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4239_, lean_object* v_x_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4239_, v_x_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v___x_4253_; 
lean_inc_ref(v_e_4247_);
v___x_4253_ = l_Lean_Meta_isProofQuick(v_e_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4280_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4256_ = v___x_4253_;
v_isShared_4257_ = v_isSharedCheck_4280_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4280_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
uint8_t v___x_4258_; 
v___x_4258_ = lean_unbox(v_a_4254_);
lean_dec(v_a_4254_);
switch(v___x_4258_)
{
case 0:
{
uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
lean_dec_ref(v_e_4247_);
v___x_4259_ = 0;
v___x_4260_ = lean_box(v___x_4259_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4260_);
v___x_4262_ = v___x_4256_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
case 1:
{
uint8_t v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4267_; 
lean_dec_ref(v_e_4247_);
v___x_4264_ = 1;
v___x_4265_ = lean_box(v___x_4264_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4265_);
v___x_4267_ = v___x_4256_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
default: 
{
lean_object* v___x_4269_; 
lean_del_object(v___x_4256_);
lean_inc(v_a_4251_);
lean_inc_ref(v_a_4250_);
lean_inc(v_a_4249_);
lean_inc_ref(v_a_4248_);
v___x_4269_ = lean_infer_type(v_e_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4271_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref(v___x_4269_);
v___x_4271_ = l_Lean_Meta_isProp(v_a_4270_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_);
return v___x_4271_;
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_a_4272_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4269_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4269_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_e_4247_);
v_a_4281_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4253_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4253_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l_Lean_Meta_isProof(v_e_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v_a_4291_);
lean_dec_ref(v_a_4290_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4296_, lean_object* v_x_4297_){
_start:
{
switch(lean_obj_tag(v_x_4296_))
{
case 3:
{
lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = lean_nat_dec_eq(v_x_4297_, v___x_4303_);
lean_dec(v_x_4297_);
if (v___x_4304_ == 0)
{
goto v___jp_4299_;
}
else
{
uint8_t v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4305_ = 1;
v___x_4306_ = lean_box(v___x_4305_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
return v___x_4307_;
}
}
case 7:
{
lean_object* v_body_4308_; lean_object* v_zero_4309_; uint8_t v_isZero_4310_; 
v_body_4308_ = lean_ctor_get(v_x_4296_, 2);
v_zero_4309_ = lean_unsigned_to_nat(0u);
v_isZero_4310_ = lean_nat_dec_eq(v_x_4297_, v_zero_4309_);
if (v_isZero_4310_ == 1)
{
uint8_t v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
lean_dec(v_x_4297_);
v___x_4311_ = 0;
v___x_4312_ = lean_box(v___x_4311_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
else
{
lean_object* v_one_4314_; lean_object* v_n_4315_; 
v_one_4314_ = lean_unsigned_to_nat(1u);
v_n_4315_ = lean_nat_sub(v_x_4297_, v_one_4314_);
lean_dec(v_x_4297_);
v_x_4296_ = v_body_4308_;
v_x_4297_ = v_n_4315_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4317_; 
v_body_4317_ = lean_ctor_get(v_x_4296_, 3);
v_x_4296_ = v_body_4317_;
goto _start;
}
case 10:
{
lean_object* v_expr_4319_; 
v_expr_4319_ = lean_ctor_get(v_x_4296_, 1);
v_x_4296_ = v_expr_4319_;
goto _start;
}
default: 
{
lean_dec(v_x_4297_);
goto v___jp_4299_;
}
}
v___jp_4299_:
{
uint8_t v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = 2;
v___x_4301_ = lean_box(v___x_4300_);
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
return v___x_4302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4321_, lean_object* v_x_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4321_, v_x_4322_);
lean_dec_ref(v_x_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4325_, lean_object* v_x_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4325_, v_x_4326_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4333_, lean_object* v_x_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4333_, v_x_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec_ref(v_x_4333_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4341_, lean_object* v_x_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_){
_start:
{
switch(lean_obj_tag(v_x_4341_))
{
case 4:
{
lean_object* v_declName_4348_; lean_object* v_us_4349_; lean_object* v___x_4350_; 
v_declName_4348_ = lean_ctor_get(v_x_4341_, 0);
lean_inc(v_declName_4348_);
v_us_4349_ = lean_ctor_get(v_x_4341_, 1);
lean_inc(v_us_4349_);
lean_dec_ref(v_x_4341_);
v___x_4350_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4348_, v_us_4349_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref(v___x_4350_);
v___x_4352_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4351_, v_x_4342_);
lean_dec(v_a_4351_);
return v___x_4352_;
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
lean_dec(v_x_4342_);
v_a_4353_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4350_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4350_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4361_; lean_object* v___x_4362_; 
v_fvarId_4361_ = lean_ctor_get(v_x_4341_, 0);
lean_inc(v_fvarId_4361_);
lean_dec_ref(v_x_4341_);
v___x_4362_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4361_, v_a_4343_, v_a_4345_, v_a_4346_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4364_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref(v___x_4362_);
v___x_4364_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4363_, v_x_4342_);
lean_dec(v_a_4363_);
return v___x_4364_;
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_x_4342_);
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
case 2:
{
lean_object* v_mvarId_4373_; lean_object* v___x_4374_; 
v_mvarId_4373_ = lean_ctor_get(v_x_4341_, 0);
lean_inc(v_mvarId_4373_);
lean_dec_ref(v_x_4341_);
v___x_4374_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4373_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref(v___x_4374_);
v___x_4376_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4375_, v_x_4342_);
lean_dec(v_a_4375_);
return v___x_4376_;
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_x_4342_);
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
case 5:
{
lean_object* v_fn_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_fn_4385_ = lean_ctor_get(v_x_4341_, 0);
lean_inc_ref(v_fn_4385_);
lean_dec_ref(v_x_4341_);
v___x_4386_ = lean_unsigned_to_nat(1u);
v___x_4387_ = lean_nat_add(v_x_4342_, v___x_4386_);
lean_dec(v_x_4342_);
v_x_4341_ = v_fn_4385_;
v_x_4342_ = v___x_4387_;
goto _start;
}
case 10:
{
lean_object* v_expr_4389_; 
v_expr_4389_ = lean_ctor_get(v_x_4341_, 1);
lean_inc_ref(v_expr_4389_);
lean_dec_ref(v_x_4341_);
v_x_4341_ = v_expr_4389_;
goto _start;
}
case 8:
{
lean_object* v_body_4391_; 
v_body_4391_ = lean_ctor_get(v_x_4341_, 3);
lean_inc_ref(v_body_4391_);
lean_dec_ref(v_x_4341_);
v_x_4341_ = v_body_4391_;
goto _start;
}
case 6:
{
lean_object* v_body_4393_; lean_object* v_zero_4394_; uint8_t v_isZero_4395_; 
v_body_4393_ = lean_ctor_get(v_x_4341_, 2);
lean_inc_ref(v_body_4393_);
lean_dec_ref(v_x_4341_);
v_zero_4394_ = lean_unsigned_to_nat(0u);
v_isZero_4395_ = lean_nat_dec_eq(v_x_4342_, v_zero_4394_);
if (v_isZero_4395_ == 1)
{
uint8_t v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
lean_dec_ref(v_body_4393_);
lean_dec(v_x_4342_);
v___x_4396_ = 0;
v___x_4397_ = lean_box(v___x_4396_);
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
return v___x_4398_;
}
else
{
lean_object* v_one_4399_; lean_object* v_n_4400_; 
v_one_4399_ = lean_unsigned_to_nat(1u);
v_n_4400_ = lean_nat_sub(v_x_4342_, v_one_4399_);
lean_dec(v_x_4342_);
v_x_4341_ = v_body_4393_;
v_x_4342_ = v_n_4400_;
goto _start;
}
}
default: 
{
uint8_t v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_dec(v_x_4342_);
lean_dec_ref(v_x_4341_);
v___x_4402_ = 2;
v___x_4403_ = lean_box(v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4405_, lean_object* v_x_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4405_, v_x_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
switch(lean_obj_tag(v_x_4413_))
{
case 1:
{
lean_object* v_fvarId_4419_; lean_object* v___x_4420_; 
v_fvarId_4419_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_fvarId_4419_);
lean_dec_ref(v_x_4413_);
v___x_4420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4419_, v_a_4414_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref(v___x_4420_);
v___x_4422_ = lean_unsigned_to_nat(0u);
v___x_4423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4421_, v___x_4422_);
lean_dec(v_a_4421_);
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
lean_dec_ref(v_x_4413_);
v___x_4433_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4432_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref(v___x_4433_);
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4434_, v___x_4435_);
lean_dec(v_a_4434_);
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
lean_dec_ref(v_x_4413_);
v___x_4445_ = 1;
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
lean_dec_ref(v_x_4413_);
v___x_4450_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4448_, v_us_4449_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4451_);
lean_dec_ref(v___x_4450_);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4451_, v___x_4452_);
lean_dec(v_a_4451_);
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
lean_dec_ref(v_x_4413_);
v___x_4463_ = lean_unsigned_to_nat(1u);
v___x_4464_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4462_, v___x_4463_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4464_;
}
case 6:
{
uint8_t v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
lean_dec_ref(v_x_4413_);
v___x_4465_ = 0;
v___x_4466_ = lean_box(v___x_4465_);
v___x_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
return v___x_4467_;
}
case 7:
{
uint8_t v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_dec_ref(v_x_4413_);
v___x_4468_ = 1;
v___x_4469_ = lean_box(v___x_4468_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
case 8:
{
lean_object* v_body_4471_; 
v_body_4471_ = lean_ctor_get(v_x_4413_, 3);
lean_inc_ref(v_body_4471_);
lean_dec_ref(v_x_4413_);
v_x_4413_ = v_body_4471_;
goto _start;
}
case 9:
{
uint8_t v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec_ref(v_x_4413_);
v___x_4473_ = 0;
v___x_4474_ = lean_box(v___x_4473_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
return v___x_4475_;
}
case 10:
{
lean_object* v_expr_4476_; 
v_expr_4476_ = lean_ctor_get(v_x_4413_, 1);
lean_inc_ref(v_expr_4476_);
lean_dec_ref(v_x_4413_);
v_x_4413_ = v_expr_4476_;
goto _start;
}
default: 
{
uint8_t v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
lean_dec_ref(v_x_4413_);
v___x_4478_ = 2;
v___x_4479_ = lean_box(v___x_4478_);
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Lean_Meta_isTypeQuick(v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v___x_4494_; 
lean_inc_ref(v_e_4488_);
v___x_4494_ = l_Lean_Meta_isTypeQuick(v_e_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4544_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4544_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4544_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
uint8_t v___x_4499_; 
v___x_4499_ = lean_unbox(v_a_4495_);
lean_dec(v_a_4495_);
switch(v___x_4499_)
{
case 0:
{
uint8_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_dec_ref(v_e_4488_);
v___x_4500_ = 0;
v___x_4501_ = lean_box(v___x_4500_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4501_);
v___x_4503_ = v___x_4497_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
case 1:
{
uint8_t v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
lean_dec_ref(v_e_4488_);
v___x_4505_ = 1;
v___x_4506_ = lean_box(v___x_4505_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4506_);
v___x_4508_ = v___x_4497_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
default: 
{
lean_object* v___x_4510_; 
lean_del_object(v___x_4497_);
lean_inc(v_a_4492_);
lean_inc_ref(v_a_4491_);
lean_inc(v_a_4490_);
lean_inc_ref(v_a_4489_);
v___x_4510_ = lean_infer_type(v_e_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4512_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref(v___x_4510_);
v___x_4512_ = l_Lean_Meta_whnfD(v_a_4511_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4527_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4515_ = v___x_4512_;
v_isShared_4516_ = v_isSharedCheck_4527_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4512_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4527_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
if (lean_obj_tag(v_a_4513_) == 3)
{
uint8_t v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
lean_dec_ref(v_a_4513_);
v___x_4517_ = 1;
v___x_4518_ = lean_box(v___x_4517_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4518_);
v___x_4520_ = v___x_4515_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
else
{
uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4525_; 
lean_dec(v_a_4513_);
v___x_4522_ = 0;
v___x_4523_ = lean_box(v___x_4522_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4523_);
v___x_4525_ = v___x_4515_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
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
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
v_a_4528_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4512_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4512_);
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
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
v_a_4536_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4510_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4510_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v_e_4488_);
v_a_4545_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4494_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4494_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Meta_isType(v_e_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4560_){
_start:
{
switch(lean_obj_tag(v_x_4560_))
{
case 7:
{
lean_object* v_body_4561_; 
v_body_4561_ = lean_ctor_get(v_x_4560_, 2);
v_x_4560_ = v_body_4561_;
goto _start;
}
case 3:
{
lean_object* v_u_4563_; lean_object* v___x_4564_; 
v_u_4563_ = lean_ctor_get(v_x_4560_, 0);
lean_inc(v_u_4563_);
v___x_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4564_, 0, v_u_4563_);
return v___x_4564_;
}
default: 
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_box(0);
return v___x_4565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4566_);
lean_dec_ref(v_x_4566_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4568_, lean_object* v_body_4569_, lean_object* v_x_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4568_, v_body_4569_, v_x_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4579_, lean_object* v_xs_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
switch(lean_obj_tag(v_type_4579_))
{
case 3:
{
lean_object* v_u_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
lean_dec_ref(v_xs_4580_);
v_u_4586_ = lean_ctor_get(v_type_4579_, 0);
lean_inc(v_u_4586_);
lean_dec_ref(v_type_4579_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v_u_4586_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
case 7:
{
lean_object* v_binderName_4589_; lean_object* v_binderType_4590_; lean_object* v_body_4591_; uint8_t v_binderInfo_4592_; lean_object* v___f_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v_binderName_4589_ = lean_ctor_get(v_type_4579_, 0);
lean_inc(v_binderName_4589_);
v_binderType_4590_ = lean_ctor_get(v_type_4579_, 1);
lean_inc_ref(v_binderType_4590_);
v_body_4591_ = lean_ctor_get(v_type_4579_, 2);
lean_inc_ref(v_body_4591_);
v_binderInfo_4592_ = lean_ctor_get_uint8(v_type_4579_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_4579_);
lean_inc_ref(v_xs_4580_);
v___f_4593_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4593_, 0, v_xs_4580_);
lean_closure_set(v___f_4593_, 1, v_body_4591_);
v___x_4594_ = lean_expr_instantiate_rev(v_binderType_4590_, v_xs_4580_);
lean_dec_ref(v_xs_4580_);
lean_dec_ref(v_binderType_4590_);
v___x_4595_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4589_, v_binderInfo_4592_, v___x_4594_, v___f_4593_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
return v___x_4595_;
}
default: 
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_expr_instantiate_rev(v_type_4579_, v_xs_4580_);
lean_dec_ref(v_xs_4580_);
lean_dec_ref(v_type_4579_);
v___x_4597_ = l_Lean_Meta_whnfD(v___x_4596_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4613_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4613_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4613_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
switch(lean_obj_tag(v_a_4598_))
{
case 3:
{
lean_object* v_u_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v_u_4602_ = lean_ctor_get(v_a_4598_, 0);
lean_inc(v_u_4602_);
lean_dec_ref(v_a_4598_);
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_u_4602_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4603_);
v___x_4605_ = v___x_4600_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
case 7:
{
lean_object* v___x_4607_; 
lean_del_object(v___x_4600_);
v___x_4607_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4579_ = v_a_4598_;
v_xs_4580_ = v___x_4607_;
goto _start;
}
default: 
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
lean_dec(v_a_4598_);
v___x_4609_ = lean_box(0);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4609_);
v___x_4611_ = v___x_4600_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
v_a_4614_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4597_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4597_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4622_, lean_object* v_body_4623_, lean_object* v_x_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = lean_array_push(v_xs_4622_, v_x_4624_);
v___x_4631_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4623_, v___x_4630_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4632_, lean_object* v_xs_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4632_, v_xs_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4640_, lean_object* v_cache_4641_, lean_object* v_a_x3f_4642_){
_start:
{
lean_object* v___x_4644_; lean_object* v_mctx_4645_; lean_object* v_zetaDeltaFVarIds_4646_; lean_object* v_postponed_4647_; lean_object* v_diag_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4658_; 
v___x_4644_ = lean_st_ref_take(v_a_4640_);
v_mctx_4645_ = lean_ctor_get(v___x_4644_, 0);
v_zetaDeltaFVarIds_4646_ = lean_ctor_get(v___x_4644_, 2);
v_postponed_4647_ = lean_ctor_get(v___x_4644_, 3);
v_diag_4648_ = lean_ctor_get(v___x_4644_, 4);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4658_ == 0)
{
lean_object* v_unused_4659_; 
v_unused_4659_ = lean_ctor_get(v___x_4644_, 1);
lean_dec(v_unused_4659_);
v___x_4650_ = v___x_4644_;
v_isShared_4651_ = v_isSharedCheck_4658_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_diag_4648_);
lean_inc(v_postponed_4647_);
lean_inc(v_zetaDeltaFVarIds_4646_);
lean_inc(v_mctx_4645_);
lean_dec(v___x_4644_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4658_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 1, v_cache_4641_);
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_mctx_4645_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v_cache_4641_);
lean_ctor_set(v_reuseFailAlloc_4657_, 2, v_zetaDeltaFVarIds_4646_);
lean_ctor_set(v_reuseFailAlloc_4657_, 3, v_postponed_4647_);
lean_ctor_set(v_reuseFailAlloc_4657_, 4, v_diag_4648_);
v___x_4653_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = lean_st_ref_set(v_a_4640_, v___x_4653_);
v___x_4655_ = lean_box(0);
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
return v___x_4656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4660_, lean_object* v_cache_4661_, lean_object* v_a_x3f_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4660_, v_cache_4661_, v_a_x3f_4662_);
lean_dec(v_a_x3f_4662_);
lean_dec(v_a_4660_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4665_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v___x_4672_; lean_object* v_cache_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4672_ = lean_st_ref_get(v_a_4667_);
v_cache_4673_ = lean_ctor_get(v___x_4672_, 1);
lean_inc_ref(v_cache_4673_);
lean_dec(v___x_4672_);
v___x_4674_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4675_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4665_, v___x_4674_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4692_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4692_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4692_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
lean_inc(v_a_4676_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set_tag(v___x_4678_, 1);
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
v___x_4682_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4667_, v_cache_4673_, v___x_4681_);
lean_dec_ref(v___x_4681_);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4689_ == 0)
{
lean_object* v_unused_4690_; 
v_unused_4690_ = lean_ctor_get(v___x_4682_, 0);
lean_dec(v_unused_4690_);
v___x_4684_ = v___x_4682_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_dec(v___x_4682_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v_a_4676_);
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4676_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
v_a_4693_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4693_);
lean_dec_ref(v___x_4675_);
v___x_4694_ = lean_box(0);
v___x_4695_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4667_, v_cache_4673_, v___x_4694_);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; 
v_unused_4703_ = lean_ctor_get(v___x_4695_, 0);
lean_dec(v_unused_4703_);
v___x_4697_ = v___x_4695_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_dec(v___x_4695_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
lean_ctor_set_tag(v___x_4697_, 1);
lean_ctor_set(v___x_4697_, 0, v_a_4693_);
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4693_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
else
{
lean_object* v___x_4704_; 
lean_dec_ref(v_type_4665_);
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4671_);
return v___x_4704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_a_4707_);
lean_dec_ref(v_a_4706_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4733_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4721_ = v___x_4718_;
v_isShared_4722_ = v_isSharedCheck_4733_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4718_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4733_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
if (lean_obj_tag(v_a_4719_) == 0)
{
uint8_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4726_; 
v___x_4723_ = 0;
v___x_4724_ = lean_box(v___x_4723_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 0, v___x_4724_);
v___x_4726_ = v___x_4721_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4724_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
else
{
uint8_t v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4731_; 
lean_dec_ref(v_a_4719_);
v___x_4728_ = 1;
v___x_4729_ = lean_box(v___x_4728_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 0, v___x_4729_);
v___x_4731_ = v___x_4721_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4729_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
v_a_4734_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4718_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4718_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l_Lean_Meta_isTypeFormerType(v_type_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
lean_dec(v_a_4746_);
lean_dec_ref(v_a_4745_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
return v_res_4748_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_4749_, lean_object* v_x_4750_){
_start:
{
if (lean_obj_tag(v_x_4749_) == 0)
{
if (lean_obj_tag(v_x_4750_) == 0)
{
uint8_t v___x_4751_; 
v___x_4751_ = 1;
return v___x_4751_;
}
else
{
uint8_t v___x_4752_; 
v___x_4752_ = 0;
return v___x_4752_;
}
}
else
{
if (lean_obj_tag(v_x_4750_) == 0)
{
uint8_t v___x_4753_; 
v___x_4753_ = 0;
return v___x_4753_;
}
else
{
lean_object* v_val_4754_; lean_object* v_val_4755_; uint8_t v___x_4756_; 
v_val_4754_ = lean_ctor_get(v_x_4749_, 0);
v_val_4755_ = lean_ctor_get(v_x_4750_, 0);
v___x_4756_ = lean_level_eq(v_val_4754_, v_val_4755_);
return v___x_4756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_4757_, lean_object* v_x_4758_){
_start:
{
uint8_t v_res_4759_; lean_object* v_r_4760_; 
v_res_4759_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_4757_, v_x_4758_);
lean_dec(v_x_4758_);
lean_dec(v_x_4757_);
v_r_4760_ = lean_box(v_res_4759_);
return v_r_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4780_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4780_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4780_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4774_; uint8_t v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4778_; 
v___x_4774_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_4775_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_4770_, v___x_4774_);
lean_dec(v_a_4770_);
v___x_4776_ = lean_box(v___x_4775_);
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v___x_4776_);
v___x_4778_ = v___x_4772_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
v_a_4781_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4769_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4769_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l_Lean_Meta_isPropFormerType(v_type_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_);
lean_dec(v_a_4793_);
lean_dec_ref(v_a_4792_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v___x_4802_; 
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
lean_inc(v_a_4798_);
lean_inc_ref(v_a_4797_);
v___x_4802_ = lean_infer_type(v_e_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4804_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_a_4803_);
lean_dec_ref(v___x_4802_);
v___x_4804_ = l_Lean_Meta_isTypeFormerType(v_a_4803_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
return v___x_4804_;
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
v_a_4805_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4802_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4802_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_Meta_isTypeFormer(v_e_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_4820_, lean_object* v_maxFVars_x3f_4821_, lean_object* v_k_4822_, uint8_t v_cleanupAnnotations_4823_, uint8_t v_whnfType_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v___f_4830_; lean_object* v___x_4831_; 
v___f_4830_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4830_, 0, v_k_4822_);
v___x_4831_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4820_, v_maxFVars_x3f_4821_, v___f_4830_, v_cleanupAnnotations_4823_, v_whnfType_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4831_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4831_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
v_a_4840_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4831_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4831_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_4848_, lean_object* v_maxFVars_x3f_4849_, lean_object* v_k_4850_, lean_object* v_cleanupAnnotations_4851_, lean_object* v_whnfType_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4858_; uint8_t v_whnfType_boxed_4859_; lean_object* v_res_4860_; 
v_cleanupAnnotations_boxed_4858_ = lean_unbox(v_cleanupAnnotations_4851_);
v_whnfType_boxed_4859_ = lean_unbox(v_whnfType_4852_);
v_res_4860_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4848_, v_maxFVars_x3f_4849_, v_k_4850_, v_cleanupAnnotations_boxed_4858_, v_whnfType_boxed_4859_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_4861_, lean_object* v_type_4862_, lean_object* v_maxFVars_x3f_4863_, lean_object* v_k_4864_, uint8_t v_cleanupAnnotations_4865_, uint8_t v_whnfType_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4862_, v_maxFVars_x3f_4863_, v_k_4864_, v_cleanupAnnotations_4865_, v_whnfType_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_4873_, lean_object* v_type_4874_, lean_object* v_maxFVars_x3f_4875_, lean_object* v_k_4876_, lean_object* v_cleanupAnnotations_4877_, lean_object* v_whnfType_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4884_; uint8_t v_whnfType_boxed_4885_; lean_object* v_res_4886_; 
v_cleanupAnnotations_boxed_4884_ = lean_unbox(v_cleanupAnnotations_4877_);
v_whnfType_boxed_4885_ = lean_unbox(v_whnfType_4878_);
v_res_4886_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_4873_, v_type_4874_, v_maxFVars_x3f_4875_, v_k_4876_, v_cleanupAnnotations_boxed_4884_, v_whnfType_boxed_4885_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
return v_res_4886_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_4887_, lean_object* v_as_4888_, size_t v_i_4889_, size_t v_stop_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_usize_dec_eq(v_i_4889_, v_stop_4890_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4892_ = lean_array_uget_borrowed(v_as_4888_, v_i_4889_);
v___x_4893_ = lean_expr_eqv(v_a_4887_, v___x_4892_);
if (v___x_4893_ == 0)
{
size_t v___x_4894_; size_t v___x_4895_; 
v___x_4894_ = ((size_t)1ULL);
v___x_4895_ = lean_usize_add(v_i_4889_, v___x_4894_);
v_i_4889_ = v___x_4895_;
goto _start;
}
else
{
return v___x_4893_;
}
}
else
{
uint8_t v___x_4897_; 
v___x_4897_ = 0;
return v___x_4897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_4898_, lean_object* v_as_4899_, lean_object* v_i_4900_, lean_object* v_stop_4901_){
_start:
{
size_t v_i_boxed_4902_; size_t v_stop_boxed_4903_; uint8_t v_res_4904_; lean_object* v_r_4905_; 
v_i_boxed_4902_ = lean_unbox_usize(v_i_4900_);
lean_dec(v_i_4900_);
v_stop_boxed_4903_ = lean_unbox_usize(v_stop_4901_);
lean_dec(v_stop_4901_);
v_res_4904_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4898_, v_as_4899_, v_i_boxed_4902_, v_stop_boxed_4903_);
lean_dec_ref(v_as_4899_);
lean_dec_ref(v_a_4898_);
v_r_4905_ = lean_box(v_res_4904_);
return v_r_4905_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; 
v___x_4908_ = lean_unsigned_to_nat(0u);
v___x_4909_ = lean_array_get_size(v_as_4906_);
v___x_4910_ = lean_nat_dec_lt(v___x_4908_, v___x_4909_);
if (v___x_4910_ == 0)
{
return v___x_4910_;
}
else
{
if (v___x_4910_ == 0)
{
return v___x_4910_;
}
else
{
size_t v___x_4911_; size_t v___x_4912_; uint8_t v___x_4913_; 
v___x_4911_ = ((size_t)0ULL);
v___x_4912_ = lean_usize_of_nat(v___x_4909_);
v___x_4913_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4907_, v_as_4906_, v___x_4911_, v___x_4912_);
return v___x_4913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_4914_, lean_object* v_a_4915_){
_start:
{
uint8_t v_res_4916_; lean_object* v_r_4917_; 
v_res_4916_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_4914_, v_a_4915_);
lean_dec_ref(v_a_4915_);
lean_dec_ref(v_as_4914_);
v_r_4917_ = lean_box(v_res_4916_);
return v_r_4917_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_4918_, lean_object* v_e_4919_){
_start:
{
uint8_t v___x_4920_; lean_object* v_d_4922_; lean_object* v_b_4923_; 
v___x_4920_ = l_Lean_Expr_hasFVar(v_e_4919_);
if (v___x_4920_ == 0)
{
lean_dec_ref(v_e_4919_);
return v___x_4920_;
}
else
{
switch(lean_obj_tag(v_e_4919_))
{
case 7:
{
lean_object* v_binderType_4926_; lean_object* v_body_4927_; 
v_binderType_4926_ = lean_ctor_get(v_e_4919_, 1);
lean_inc_ref(v_binderType_4926_);
v_body_4927_ = lean_ctor_get(v_e_4919_, 2);
lean_inc_ref(v_body_4927_);
lean_dec_ref(v_e_4919_);
v_d_4922_ = v_binderType_4926_;
v_b_4923_ = v_body_4927_;
goto v___jp_4921_;
}
case 6:
{
lean_object* v_binderType_4928_; lean_object* v_body_4929_; 
v_binderType_4928_ = lean_ctor_get(v_e_4919_, 1);
lean_inc_ref(v_binderType_4928_);
v_body_4929_ = lean_ctor_get(v_e_4919_, 2);
lean_inc_ref(v_body_4929_);
lean_dec_ref(v_e_4919_);
v_d_4922_ = v_binderType_4928_;
v_b_4923_ = v_body_4929_;
goto v___jp_4921_;
}
case 10:
{
lean_object* v_expr_4930_; 
v_expr_4930_ = lean_ctor_get(v_e_4919_, 1);
lean_inc_ref(v_expr_4930_);
lean_dec_ref(v_e_4919_);
v_e_4919_ = v_expr_4930_;
goto _start;
}
case 8:
{
lean_object* v_type_4932_; lean_object* v_value_4933_; lean_object* v_body_4934_; uint8_t v___x_4935_; 
v_type_4932_ = lean_ctor_get(v_e_4919_, 1);
lean_inc_ref(v_type_4932_);
v_value_4933_ = lean_ctor_get(v_e_4919_, 2);
lean_inc_ref(v_value_4933_);
v_body_4934_ = lean_ctor_get(v_e_4919_, 3);
lean_inc_ref(v_body_4934_);
lean_dec_ref(v_e_4919_);
v___x_4935_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4918_, v_type_4932_);
if (v___x_4935_ == 0)
{
uint8_t v___x_4936_; 
v___x_4936_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4918_, v_value_4933_);
if (v___x_4936_ == 0)
{
v_e_4919_ = v_body_4934_;
goto _start;
}
else
{
lean_dec_ref(v_body_4934_);
return v___x_4920_;
}
}
else
{
lean_dec_ref(v_body_4934_);
lean_dec_ref(v_value_4933_);
return v___x_4920_;
}
}
case 5:
{
lean_object* v_fn_4938_; lean_object* v_arg_4939_; uint8_t v___x_4940_; 
v_fn_4938_ = lean_ctor_get(v_e_4919_, 0);
lean_inc_ref(v_fn_4938_);
v_arg_4939_ = lean_ctor_get(v_e_4919_, 1);
lean_inc_ref(v_arg_4939_);
lean_dec_ref(v_e_4919_);
v___x_4940_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4918_, v_fn_4938_);
if (v___x_4940_ == 0)
{
v_e_4919_ = v_arg_4939_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4939_);
return v___x_4920_;
}
}
case 11:
{
lean_object* v_struct_4942_; 
v_struct_4942_ = lean_ctor_get(v_e_4919_, 2);
lean_inc_ref(v_struct_4942_);
lean_dec_ref(v_e_4919_);
v_e_4919_ = v_struct_4942_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4944_; lean_object* v___x_4945_; uint8_t v___x_4946_; 
v_fvarId_4944_ = lean_ctor_get(v_e_4919_, 0);
lean_inc(v_fvarId_4944_);
lean_dec_ref(v_e_4919_);
v___x_4945_ = l_Lean_Expr_fvar___override(v_fvarId_4944_);
v___x_4946_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_4918_, v___x_4945_);
lean_dec_ref(v___x_4945_);
return v___x_4946_;
}
default: 
{
uint8_t v___x_4947_; 
lean_dec_ref(v_e_4919_);
v___x_4947_ = 0;
return v___x_4947_;
}
}
}
v___jp_4921_:
{
uint8_t v___x_4924_; 
v___x_4924_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4918_, v_d_4922_);
if (v___x_4924_ == 0)
{
v_e_4919_ = v_b_4923_;
goto _start;
}
else
{
lean_dec_ref(v_b_4923_);
return v___x_4920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_4948_, lean_object* v_e_4949_){
_start:
{
uint8_t v_res_4950_; lean_object* v_r_4951_; 
v_res_4950_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4948_, v_e_4949_);
lean_dec_ref(v_xs_4948_);
v_r_4951_ = lean_box(v_res_4950_);
return v_r_4951_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_4954_ = l_Lean_stringToMessageData(v___x_4953_);
return v___x_4954_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_4957_ = l_Lean_stringToMessageData(v___x_4956_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_4958_, lean_object* v_type_4959_, lean_object* v_as_4960_, size_t v_sz_4961_, size_t v_i_4962_, lean_object* v_b_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v_a_4970_; uint8_t v___x_4974_; 
v___x_4974_ = lean_usize_dec_lt(v_i_4962_, v_sz_4961_);
if (v___x_4974_ == 0)
{
lean_object* v___x_4975_; 
lean_dec_ref(v_type_4959_);
v___x_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4975_, 0, v_b_4963_);
return v___x_4975_;
}
else
{
lean_object* v___x_4976_; lean_object* v_a_4977_; uint8_t v___x_4978_; 
v___x_4976_ = lean_box(0);
v_a_4977_ = lean_array_uget_borrowed(v_as_4960_, v_i_4962_);
lean_inc(v_a_4977_);
v___x_4978_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4958_, v_a_4977_);
if (v___x_4978_ == 0)
{
v_a_4970_ = v___x_4976_;
goto v___jp_4969_;
}
else
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4979_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_4977_);
v___x_4980_ = l_Lean_MessageData_ofExpr(v_a_4977_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_4983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4981_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
lean_inc_ref(v_type_4959_);
v___x_4984_ = l_Lean_MessageData_ofExpr(v_type_4959_);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4983_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
v___x_4986_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_4985_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_dec_ref(v___x_4986_);
v_a_4970_ = v___x_4976_;
goto v___jp_4969_;
}
else
{
lean_dec_ref(v_type_4959_);
return v___x_4986_;
}
}
}
v___jp_4969_:
{
size_t v___x_4971_; size_t v___x_4972_; 
v___x_4971_ = ((size_t)1ULL);
v___x_4972_ = lean_usize_add(v_i_4962_, v___x_4971_);
v_i_4962_ = v___x_4972_;
v_b_4963_ = v_a_4970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_4987_, lean_object* v_type_4988_, lean_object* v_as_4989_, lean_object* v_sz_4990_, lean_object* v_i_4991_, lean_object* v_b_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
size_t v_sz_boxed_4998_; size_t v_i_boxed_4999_; lean_object* v_res_5000_; 
v_sz_boxed_4998_ = lean_unbox_usize(v_sz_4990_);
lean_dec(v_sz_4990_);
v_i_boxed_4999_ = lean_unbox_usize(v_i_4991_);
lean_dec(v_i_4991_);
v_res_5000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_4987_, v_type_4988_, v_as_4989_, v_sz_boxed_4998_, v_i_boxed_4999_, v_b_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec_ref(v_as_4989_);
lean_dec_ref(v_xs_4987_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5001_, size_t v_i_5002_, lean_object* v_bs_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
uint8_t v___x_5009_; 
v___x_5009_ = lean_usize_dec_lt(v_i_5002_, v_sz_5001_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v_bs_5003_);
return v___x_5010_;
}
else
{
lean_object* v_v_5011_; lean_object* v___x_5012_; 
v_v_5011_ = lean_array_uget_borrowed(v_bs_5003_, v_i_5002_);
lean_inc(v___y_5007_);
lean_inc_ref(v___y_5006_);
lean_inc(v___y_5005_);
lean_inc_ref(v___y_5004_);
lean_inc(v_v_5011_);
v___x_5012_ = lean_infer_type(v_v_5011_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5014_; lean_object* v_bs_x27_5015_; size_t v___x_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref(v___x_5012_);
v___x_5014_ = lean_unsigned_to_nat(0u);
v_bs_x27_5015_ = lean_array_uset(v_bs_5003_, v_i_5002_, v___x_5014_);
v___x_5016_ = ((size_t)1ULL);
v___x_5017_ = lean_usize_add(v_i_5002_, v___x_5016_);
v___x_5018_ = lean_array_uset(v_bs_x27_5015_, v_i_5002_, v_a_5013_);
v_i_5002_ = v___x_5017_;
v_bs_5003_ = v___x_5018_;
goto _start;
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec_ref(v_bs_5003_);
v_a_5020_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_5012_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5012_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5028_, lean_object* v_i_5029_, lean_object* v_bs_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
size_t v_sz_boxed_5036_; size_t v_i_boxed_5037_; lean_object* v_res_5038_; 
v_sz_boxed_5036_ = lean_unbox_usize(v_sz_5028_);
lean_dec(v_sz_5028_);
v_i_boxed_5037_ = lean_unbox_usize(v_i_5029_);
lean_dec(v_i_5029_);
v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5036_, v_i_boxed_5037_, v_bs_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
return v_res_5038_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5041_ = l_Lean_stringToMessageData(v___x_5040_);
return v___x_5041_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5044_ = l_Lean_stringToMessageData(v___x_5043_);
return v___x_5044_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5046_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5047_ = l_Lean_stringToMessageData(v___x_5046_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5048_, lean_object* v_n_5049_, lean_object* v_xs_5050_, lean_object* v_x_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v___x_5081_; uint8_t v___x_5082_; 
v___x_5081_ = lean_array_get_size(v_xs_5050_);
v___x_5082_ = lean_nat_dec_eq(v___x_5081_, v_n_5049_);
if (v___x_5082_ == 0)
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec_ref(v_xs_5050_);
v___x_5083_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5084_ = l_Lean_MessageData_ofExpr(v_type_5048_);
v___x_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5083_);
lean_ctor_set(v___x_5085_, 1, v___x_5084_);
v___x_5086_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5085_);
lean_ctor_set(v___x_5087_, 1, v___x_5086_);
v___x_5088_ = l_Nat_reprFast(v_n_5049_);
v___x_5089_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5088_);
v___x_5090_ = l_Lean_MessageData_ofFormat(v___x_5089_);
v___x_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5087_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
v___x_5092_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5091_);
lean_ctor_set(v___x_5093_, 1, v___x_5092_);
v___x_5094_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5093_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5094_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5094_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
else
{
lean_dec(v_n_5049_);
goto v___jp_5057_;
}
v___jp_5057_:
{
size_t v_sz_5058_; size_t v___x_5059_; lean_object* v___x_5060_; 
v_sz_5058_ = lean_array_size(v_xs_5050_);
v___x_5059_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5050_);
v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5058_, v___x_5059_, v_xs_5050_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5062_; size_t v_sz_5063_; lean_object* v___x_5064_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref(v___x_5060_);
v___x_5062_ = lean_box(0);
v_sz_5063_ = lean_array_size(v_a_5061_);
v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5050_, v_type_5048_, v_a_5061_, v_sz_5063_, v___x_5059_, v___x_5062_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec_ref(v_xs_5050_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5071_ == 0)
{
lean_object* v_unused_5072_; 
v_unused_5072_ = lean_ctor_get(v___x_5064_, 0);
lean_dec(v_unused_5072_);
v___x_5066_ = v___x_5064_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_dec(v___x_5064_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 0, v_a_5061_);
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5061_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_dec(v_a_5061_);
v_a_5073_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5064_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5064_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5050_);
lean_dec_ref(v_type_5048_);
return v___x_5060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5103_, lean_object* v_n_5104_, lean_object* v_xs_5105_, lean_object* v_x_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5103_, v_n_5104_, v_xs_5105_, v_x_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec_ref(v_x_5106_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5113_, lean_object* v_type_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v___f_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; lean_object* v___x_5123_; 
lean_inc(v_n_5113_);
lean_inc_ref(v_type_5114_);
v___f_5120_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5120_, 0, v_type_5114_);
lean_closure_set(v___f_5120_, 1, v_n_5113_);
v___x_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5121_, 0, v_n_5113_);
v___x_5122_ = 0;
v___x_5123_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5114_, v___x_5121_, v___f_5120_, v___x_5122_, v___x_5122_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5124_, lean_object* v_type_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Lean_Meta_arrowDomainsN(v_n_5124_, v_type_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_);
lean_dec(v_a_5129_);
lean_dec_ref(v_a_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5132_, lean_object* v_e_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_){
_start:
{
lean_object* v___x_5139_; 
lean_inc(v_a_5137_);
lean_inc_ref(v_a_5136_);
lean_inc(v_a_5135_);
lean_inc_ref(v_a_5134_);
v___x_5139_ = lean_infer_type(v_e_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5141_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref(v___x_5139_);
v___x_5141_ = l_Lean_Meta_arrowDomainsN(v_n_5132_, v_a_5140_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_);
return v___x_5141_;
}
else
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
lean_dec(v_n_5132_);
v_a_5142_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5139_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5139_);
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
v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5150_, lean_object* v_e_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Meta_inferArgumentTypesN(v_n_5150_, v_e_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_);
lean_dec(v_a_5155_);
lean_dec_ref(v_a_5154_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5152_);
return v_res_5157_;
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
