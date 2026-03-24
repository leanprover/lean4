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
v___x_4201__overap_34_ = lean_panic_fn(v___x_33_, v_msg_13_);
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
lean_inc(v_offset_297_);
lean_inc_ref(v_type_384_);
v___x_388_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_type_384_, v_offset_297_, v_a_298_);
v_fst_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v___x_388_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v___x_388_);
lean_inc(v_offset_297_);
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
v___x_531_ = lean_panic_fn(v___x_530_, v_msg_529_);
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
lean_inc(v_mvarId_1827_);
lean_dec_ref(v_a_1819_);
lean_inc(v_mvarId_1827_);
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
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
lean_inc(v_a_1832_);
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
lean_inc_ref(v_lctx_2306_);
lean_dec_ref(v_a_2302_);
lean_inc(v_fvarId_2301_);
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
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; 
lean_inc_ref(v_a_2325_);
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
uint8_t v___y_2429_; lean_object* v___y_2430_; uint8_t v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; uint8_t v___y_2436_; lean_object* v___y_2437_; uint8_t v___y_2438_; lean_object* v___y_2439_; uint8_t v___y_2468_; lean_object* v___x_2535_; uint8_t v_transparency_2536_; uint8_t v___x_2537_; uint8_t v___x_2538_; 
v___x_2535_ = l_Lean_Meta_Context_config(v_a_2423_);
v_transparency_2536_ = lean_ctor_get_uint8(v___x_2535_, 9);
lean_dec_ref(v___x_2535_);
v___x_2537_ = 1;
v___x_2538_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
v___y_2468_ = v_transparency_2536_;
goto v___jp_2467_;
}
else
{
v___y_2468_ = v___x_2537_;
goto v___jp_2467_;
}
v___jp_2428_:
{
lean_object* v___x_2440_; uint8_t v_foApprox_2441_; uint8_t v_ctxApprox_2442_; uint8_t v_quasiPatternApprox_2443_; uint8_t v_constApprox_2444_; uint8_t v_isDefEqStuckEx_2445_; uint8_t v_unificationHints_2446_; uint8_t v_proofIrrelevance_2447_; uint8_t v_assignSyntheticOpaque_2448_; uint8_t v_offsetCnstrs_2449_; uint8_t v_transparency_2450_; uint8_t v_univApprox_2451_; uint8_t v_zetaUnused_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2466_; 
v___x_2440_ = l_Lean_Meta_Context_config(v___y_2435_);
lean_dec_ref(v___y_2435_);
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
lean_inc(v___y_2430_);
lean_inc(v___y_2432_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2434_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2433_);
v___x_2463_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___y_2433_);
lean_ctor_set(v___x_2463_, 2, v___y_2439_);
lean_ctor_set(v___x_2463_, 3, v___y_2434_);
lean_ctor_set(v___x_2463_, 4, v___y_2437_);
lean_ctor_set(v___x_2463_, 5, v___y_2432_);
lean_ctor_set(v___x_2463_, 6, v___y_2430_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7, v___y_2431_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7 + 1, v___y_2429_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7 + 2, v___y_2438_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*7 + 3, v___y_2436_);
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
lean_object* v___x_2469_; uint8_t v_foApprox_2470_; uint8_t v_ctxApprox_2471_; uint8_t v_quasiPatternApprox_2472_; uint8_t v_constApprox_2473_; uint8_t v_isDefEqStuckEx_2474_; uint8_t v_unificationHints_2475_; uint8_t v_proofIrrelevance_2476_; uint8_t v_assignSyntheticOpaque_2477_; uint8_t v_offsetCnstrs_2478_; uint8_t v_etaStruct_2479_; uint8_t v_univApprox_2480_; uint8_t v_iota_2481_; uint8_t v_beta_2482_; uint8_t v_proj_2483_; uint8_t v_zeta_2484_; uint8_t v_zetaDelta_2485_; uint8_t v_zetaUnused_2486_; uint8_t v_zetaHave_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2534_; 
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
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2489_ = v___x_2469_;
v_isShared_2490_ = v_isSharedCheck_2534_;
goto v_resetjp_2488_;
}
else
{
lean_dec(v___x_2469_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2534_;
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
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 0, v_foApprox_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 1, v_ctxApprox_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 2, v_quasiPatternApprox_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 3, v_constApprox_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 4, v_isDefEqStuckEx_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 5, v_unificationHints_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 6, v_proofIrrelevance_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 7, v_assignSyntheticOpaque_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 8, v_offsetCnstrs_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 10, v_etaStruct_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 11, v_univApprox_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 12, v_iota_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 13, v_beta_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 14, v_proj_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 15, v_zeta_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 16, v_zetaDelta_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 17, v_zetaUnused_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 18, v_zetaHave_2487_);
v_config_2502_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
uint64_t v___x_2503_; uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; uint64_t v___x_2507_; uint64_t v_key_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
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
v___x_2511_ = l_Lean_Meta_getConfig___redArg(v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; uint8_t v_beta_2513_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v_beta_2513_ = lean_ctor_get_uint8(v_a_2512_, 13);
if (v_beta_2513_ == 0)
{
lean_dec(v_a_2512_);
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
uint8_t v_iota_2514_; 
v_iota_2514_ = lean_ctor_get_uint8(v_a_2512_, 12);
if (v_iota_2514_ == 0)
{
lean_dec(v_a_2512_);
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
uint8_t v_zeta_2515_; 
v_zeta_2515_ = lean_ctor_get_uint8(v_a_2512_, 15);
if (v_zeta_2515_ == 0)
{
lean_dec(v_a_2512_);
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
uint8_t v_zetaHave_2516_; 
v_zetaHave_2516_ = lean_ctor_get_uint8(v_a_2512_, 18);
if (v_zetaHave_2516_ == 0)
{
lean_dec(v_a_2512_);
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
uint8_t v_zetaDelta_2517_; 
v_zetaDelta_2517_ = lean_ctor_get_uint8(v_a_2512_, 16);
if (v_zetaDelta_2517_ == 0)
{
lean_dec(v_a_2512_);
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
uint8_t v_etaStruct_2518_; uint8_t v_proj_2519_; uint8_t v___x_2520_; uint8_t v___x_2521_; 
v_etaStruct_2518_ = lean_ctor_get_uint8(v_a_2512_, 10);
v_proj_2519_ = lean_ctor_get_uint8(v_a_2512_, 14);
lean_dec(v_a_2512_);
v___x_2520_ = 2;
v___x_2521_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
uint8_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = 0;
v___x_2523_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2518_, v___x_2522_);
if (v___x_2523_ == 0)
{
v___y_2429_ = v_univApprox_2498_;
v___y_2430_ = v_canUnfold_x3f_2497_;
v___y_2431_ = v_trackZetaDelta_2491_;
v___y_2432_ = v_synthPendingDepth_2496_;
v___y_2433_ = v_zetaDeltaSet_2492_;
v___y_2434_ = v_localInstances_2494_;
v___y_2435_ = v___x_2510_;
v___y_2436_ = v_cacheInferType_2500_;
v___y_2437_ = v_defEqCtx_x3f_2495_;
v___y_2438_ = v_inTypeClassResolution_2499_;
v___y_2439_ = v_lctx_2493_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2524_; 
lean_inc(v_a_2426_);
lean_inc_ref(v_a_2425_);
lean_inc(v_a_2424_);
v___x_2524_ = lean_apply_5(v_x_2422_, v___x_2510_, v_a_2424_, v_a_2425_, v_a_2426_, lean_box(0));
return v___x_2524_;
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
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v___x_2510_);
lean_dec_ref(v_x_2422_);
v_a_2525_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2511_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2511_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2546_, lean_object* v_x_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
uint8_t v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; uint8_t v___y_2561_; lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2593_; lean_object* v___x_2660_; uint8_t v_transparency_2661_; uint8_t v___x_2662_; uint8_t v___x_2663_; 
v___x_2660_ = l_Lean_Meta_Context_config(v_a_2548_);
v_transparency_2661_ = lean_ctor_get_uint8(v___x_2660_, 9);
lean_dec_ref(v___x_2660_);
v___x_2662_ = 1;
v___x_2663_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
v___y_2593_ = v_transparency_2661_;
goto v___jp_2592_;
}
else
{
v___y_2593_ = v___x_2662_;
goto v___jp_2592_;
}
v___jp_2553_:
{
lean_object* v___x_2565_; uint8_t v_foApprox_2566_; uint8_t v_ctxApprox_2567_; uint8_t v_quasiPatternApprox_2568_; uint8_t v_constApprox_2569_; uint8_t v_isDefEqStuckEx_2570_; uint8_t v_unificationHints_2571_; uint8_t v_proofIrrelevance_2572_; uint8_t v_assignSyntheticOpaque_2573_; uint8_t v_offsetCnstrs_2574_; uint8_t v_transparency_2575_; uint8_t v_univApprox_2576_; uint8_t v_zetaUnused_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2591_; 
v___x_2565_ = l_Lean_Meta_Context_config(v___y_2560_);
lean_dec_ref(v___y_2560_);
v_foApprox_2566_ = lean_ctor_get_uint8(v___x_2565_, 0);
v_ctxApprox_2567_ = lean_ctor_get_uint8(v___x_2565_, 1);
v_quasiPatternApprox_2568_ = lean_ctor_get_uint8(v___x_2565_, 2);
v_constApprox_2569_ = lean_ctor_get_uint8(v___x_2565_, 3);
v_isDefEqStuckEx_2570_ = lean_ctor_get_uint8(v___x_2565_, 4);
v_unificationHints_2571_ = lean_ctor_get_uint8(v___x_2565_, 5);
v_proofIrrelevance_2572_ = lean_ctor_get_uint8(v___x_2565_, 6);
v_assignSyntheticOpaque_2573_ = lean_ctor_get_uint8(v___x_2565_, 7);
v_offsetCnstrs_2574_ = lean_ctor_get_uint8(v___x_2565_, 8);
v_transparency_2575_ = lean_ctor_get_uint8(v___x_2565_, 9);
v_univApprox_2576_ = lean_ctor_get_uint8(v___x_2565_, 11);
v_zetaUnused_2577_ = lean_ctor_get_uint8(v___x_2565_, 17);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2579_ = v___x_2565_;
v_isShared_2580_ = v_isSharedCheck_2591_;
goto v_resetjp_2578_;
}
else
{
lean_dec(v___x_2565_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2591_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
uint8_t v___x_2581_; uint8_t v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2585_; 
v___x_2581_ = 1;
v___x_2582_ = 0;
v___x_2583_ = 2;
if (v_isShared_2580_ == 0)
{
v___x_2585_ = v___x_2579_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 0, v_foApprox_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 1, v_ctxApprox_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 2, v_quasiPatternApprox_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 3, v_constApprox_2569_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 4, v_isDefEqStuckEx_2570_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 5, v_unificationHints_2571_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 6, v_proofIrrelevance_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 7, v_assignSyntheticOpaque_2573_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 8, v_offsetCnstrs_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 9, v_transparency_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 11, v_univApprox_2576_);
lean_ctor_set_uint8(v_reuseFailAlloc_2590_, 17, v_zetaUnused_2577_);
v___x_2585_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
uint64_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_ctor_set_uint8(v___x_2585_, 10, v___x_2582_);
lean_ctor_set_uint8(v___x_2585_, 12, v___x_2581_);
lean_ctor_set_uint8(v___x_2585_, 13, v___x_2581_);
lean_ctor_set_uint8(v___x_2585_, 14, v___x_2583_);
lean_ctor_set_uint8(v___x_2585_, 15, v___x_2581_);
lean_ctor_set_uint8(v___x_2585_, 16, v___x_2581_);
lean_ctor_set_uint8(v___x_2585_, 18, v___x_2581_);
v___x_2586_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set_uint64(v___x_2587_, sizeof(void*)*1, v___x_2586_);
lean_inc(v___y_2555_);
lean_inc(v___y_2557_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2559_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2558_);
v___x_2588_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___y_2558_);
lean_ctor_set(v___x_2588_, 2, v___y_2564_);
lean_ctor_set(v___x_2588_, 3, v___y_2559_);
lean_ctor_set(v___x_2588_, 4, v___y_2562_);
lean_ctor_set(v___x_2588_, 5, v___y_2557_);
lean_ctor_set(v___x_2588_, 6, v___y_2555_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*7, v___y_2556_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*7 + 1, v___y_2554_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*7 + 2, v___y_2563_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*7 + 3, v___y_2561_);
lean_inc(v_a_2551_);
lean_inc_ref(v_a_2550_);
lean_inc(v_a_2549_);
v___x_2589_ = lean_apply_5(v_x_2547_, v___x_2588_, v_a_2549_, v_a_2550_, v_a_2551_, lean_box(0));
return v___x_2589_;
}
}
}
v___jp_2592_:
{
lean_object* v___x_2594_; uint8_t v_foApprox_2595_; uint8_t v_ctxApprox_2596_; uint8_t v_quasiPatternApprox_2597_; uint8_t v_constApprox_2598_; uint8_t v_isDefEqStuckEx_2599_; uint8_t v_unificationHints_2600_; uint8_t v_proofIrrelevance_2601_; uint8_t v_assignSyntheticOpaque_2602_; uint8_t v_offsetCnstrs_2603_; uint8_t v_etaStruct_2604_; uint8_t v_univApprox_2605_; uint8_t v_iota_2606_; uint8_t v_beta_2607_; uint8_t v_proj_2608_; uint8_t v_zeta_2609_; uint8_t v_zetaDelta_2610_; uint8_t v_zetaUnused_2611_; uint8_t v_zetaHave_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2659_; 
v___x_2594_ = l_Lean_Meta_Context_config(v_a_2548_);
v_foApprox_2595_ = lean_ctor_get_uint8(v___x_2594_, 0);
v_ctxApprox_2596_ = lean_ctor_get_uint8(v___x_2594_, 1);
v_quasiPatternApprox_2597_ = lean_ctor_get_uint8(v___x_2594_, 2);
v_constApprox_2598_ = lean_ctor_get_uint8(v___x_2594_, 3);
v_isDefEqStuckEx_2599_ = lean_ctor_get_uint8(v___x_2594_, 4);
v_unificationHints_2600_ = lean_ctor_get_uint8(v___x_2594_, 5);
v_proofIrrelevance_2601_ = lean_ctor_get_uint8(v___x_2594_, 6);
v_assignSyntheticOpaque_2602_ = lean_ctor_get_uint8(v___x_2594_, 7);
v_offsetCnstrs_2603_ = lean_ctor_get_uint8(v___x_2594_, 8);
v_etaStruct_2604_ = lean_ctor_get_uint8(v___x_2594_, 10);
v_univApprox_2605_ = lean_ctor_get_uint8(v___x_2594_, 11);
v_iota_2606_ = lean_ctor_get_uint8(v___x_2594_, 12);
v_beta_2607_ = lean_ctor_get_uint8(v___x_2594_, 13);
v_proj_2608_ = lean_ctor_get_uint8(v___x_2594_, 14);
v_zeta_2609_ = lean_ctor_get_uint8(v___x_2594_, 15);
v_zetaDelta_2610_ = lean_ctor_get_uint8(v___x_2594_, 16);
v_zetaUnused_2611_ = lean_ctor_get_uint8(v___x_2594_, 17);
v_zetaHave_2612_ = lean_ctor_get_uint8(v___x_2594_, 18);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2614_ = v___x_2594_;
v_isShared_2615_ = v_isSharedCheck_2659_;
goto v_resetjp_2613_;
}
else
{
lean_dec(v___x_2594_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2659_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v_trackZetaDelta_2616_; lean_object* v_zetaDeltaSet_2617_; lean_object* v_lctx_2618_; lean_object* v_localInstances_2619_; lean_object* v_defEqCtx_x3f_2620_; lean_object* v_synthPendingDepth_2621_; lean_object* v_canUnfold_x3f_2622_; uint8_t v_univApprox_2623_; uint8_t v_inTypeClassResolution_2624_; uint8_t v_cacheInferType_2625_; lean_object* v_config_2627_; 
v_trackZetaDelta_2616_ = lean_ctor_get_uint8(v_a_2548_, sizeof(void*)*7);
v_zetaDeltaSet_2617_ = lean_ctor_get(v_a_2548_, 1);
v_lctx_2618_ = lean_ctor_get(v_a_2548_, 2);
v_localInstances_2619_ = lean_ctor_get(v_a_2548_, 3);
v_defEqCtx_x3f_2620_ = lean_ctor_get(v_a_2548_, 4);
v_synthPendingDepth_2621_ = lean_ctor_get(v_a_2548_, 5);
v_canUnfold_x3f_2622_ = lean_ctor_get(v_a_2548_, 6);
v_univApprox_2623_ = lean_ctor_get_uint8(v_a_2548_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2624_ = lean_ctor_get_uint8(v_a_2548_, sizeof(void*)*7 + 2);
v_cacheInferType_2625_ = lean_ctor_get_uint8(v_a_2548_, sizeof(void*)*7 + 3);
if (v_isShared_2615_ == 0)
{
v_config_2627_ = v___x_2614_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 0, v_foApprox_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 1, v_ctxApprox_2596_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 2, v_quasiPatternApprox_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 3, v_constApprox_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 4, v_isDefEqStuckEx_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 5, v_unificationHints_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 6, v_proofIrrelevance_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 7, v_assignSyntheticOpaque_2602_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 8, v_offsetCnstrs_2603_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 10, v_etaStruct_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 11, v_univApprox_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 12, v_iota_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 13, v_beta_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 14, v_proj_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 15, v_zeta_2609_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 16, v_zetaDelta_2610_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 17, v_zetaUnused_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2658_, 18, v_zetaHave_2612_);
v_config_2627_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
uint64_t v___x_2628_; uint64_t v___x_2629_; uint64_t v___x_2630_; uint64_t v___x_2631_; uint64_t v___x_2632_; uint64_t v_key_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_ctor_set_uint8(v_config_2627_, 9, v___y_2593_);
v___x_2628_ = l_Lean_Meta_Context_configKey(v_a_2548_);
v___x_2629_ = 2ULL;
v___x_2630_ = lean_uint64_shift_right(v___x_2628_, v___x_2629_);
v___x_2631_ = lean_uint64_shift_left(v___x_2630_, v___x_2629_);
v___x_2632_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2593_);
v_key_2633_ = lean_uint64_lor(v___x_2631_, v___x_2632_);
v___x_2634_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2634_, 0, v_config_2627_);
lean_ctor_set_uint64(v___x_2634_, sizeof(void*)*1, v_key_2633_);
lean_inc(v_canUnfold_x3f_2622_);
lean_inc(v_synthPendingDepth_2621_);
lean_inc(v_defEqCtx_x3f_2620_);
lean_inc_ref(v_localInstances_2619_);
lean_inc_ref(v_lctx_2618_);
lean_inc(v_zetaDeltaSet_2617_);
v___x_2635_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v_zetaDeltaSet_2617_);
lean_ctor_set(v___x_2635_, 2, v_lctx_2618_);
lean_ctor_set(v___x_2635_, 3, v_localInstances_2619_);
lean_ctor_set(v___x_2635_, 4, v_defEqCtx_x3f_2620_);
lean_ctor_set(v___x_2635_, 5, v_synthPendingDepth_2621_);
lean_ctor_set(v___x_2635_, 6, v_canUnfold_x3f_2622_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*7, v_trackZetaDelta_2616_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*7 + 1, v_univApprox_2623_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2624_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*7 + 3, v_cacheInferType_2625_);
v___x_2636_ = l_Lean_Meta_getConfig___redArg(v___x_2635_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; uint8_t v_beta_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v_beta_2638_ = lean_ctor_get_uint8(v_a_2637_, 13);
if (v_beta_2638_ == 0)
{
lean_dec(v_a_2637_);
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
uint8_t v_iota_2639_; 
v_iota_2639_ = lean_ctor_get_uint8(v_a_2637_, 12);
if (v_iota_2639_ == 0)
{
lean_dec(v_a_2637_);
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
uint8_t v_zeta_2640_; 
v_zeta_2640_ = lean_ctor_get_uint8(v_a_2637_, 15);
if (v_zeta_2640_ == 0)
{
lean_dec(v_a_2637_);
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
uint8_t v_zetaHave_2641_; 
v_zetaHave_2641_ = lean_ctor_get_uint8(v_a_2637_, 18);
if (v_zetaHave_2641_ == 0)
{
lean_dec(v_a_2637_);
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
uint8_t v_zetaDelta_2642_; 
v_zetaDelta_2642_ = lean_ctor_get_uint8(v_a_2637_, 16);
if (v_zetaDelta_2642_ == 0)
{
lean_dec(v_a_2637_);
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
uint8_t v_etaStruct_2643_; uint8_t v_proj_2644_; uint8_t v___x_2645_; uint8_t v___x_2646_; 
v_etaStruct_2643_ = lean_ctor_get_uint8(v_a_2637_, 10);
v_proj_2644_ = lean_ctor_get_uint8(v_a_2637_, 14);
lean_dec(v_a_2637_);
v___x_2645_ = 2;
v___x_2646_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
uint8_t v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = 0;
v___x_2648_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2643_, v___x_2647_);
if (v___x_2648_ == 0)
{
v___y_2554_ = v_univApprox_2623_;
v___y_2555_ = v_canUnfold_x3f_2622_;
v___y_2556_ = v_trackZetaDelta_2616_;
v___y_2557_ = v_synthPendingDepth_2621_;
v___y_2558_ = v_zetaDeltaSet_2617_;
v___y_2559_ = v_localInstances_2619_;
v___y_2560_ = v___x_2635_;
v___y_2561_ = v_cacheInferType_2625_;
v___y_2562_ = v_defEqCtx_x3f_2620_;
v___y_2563_ = v_inTypeClassResolution_2624_;
v___y_2564_ = v_lctx_2618_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2649_; 
lean_inc(v_a_2551_);
lean_inc_ref(v_a_2550_);
lean_inc(v_a_2549_);
v___x_2649_ = lean_apply_5(v_x_2547_, v___x_2635_, v_a_2549_, v_a_2550_, v_a_2551_, lean_box(0));
return v___x_2649_;
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
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_x_2547_);
v_a_2650_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2636_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2636_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2664_, lean_object* v_x_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2664_, v_x_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_){
_start:
{
lean_object* v_ks_2676_; lean_object* v_vs_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2706_; 
v_ks_2676_ = lean_ctor_get(v_x_2672_, 0);
v_vs_2677_ = lean_ctor_get(v_x_2672_, 1);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_x_2672_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2679_ = v_x_2672_;
v_isShared_2680_ = v_isSharedCheck_2706_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_vs_2677_);
lean_inc(v_ks_2676_);
lean_dec(v_x_2672_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2706_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
uint8_t v___y_2682_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = lean_array_get_size(v_ks_2676_);
v___x_2695_ = lean_nat_dec_lt(v_x_2673_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_del_object(v___x_2679_);
lean_dec(v_x_2673_);
v___x_2696_ = lean_array_push(v_ks_2676_, v_x_2674_);
v___x_2697_ = lean_array_push(v_vs_2677_, v_x_2675_);
v___x_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
return v___x_2698_;
}
else
{
lean_object* v_expr_2699_; uint64_t v_configKey_2700_; lean_object* v_k_x27_2701_; lean_object* v_expr_2702_; uint64_t v_configKey_2703_; uint8_t v___x_2704_; 
v_expr_2699_ = lean_ctor_get(v_x_2674_, 0);
v_configKey_2700_ = lean_ctor_get_uint64(v_x_2674_, sizeof(void*)*1);
v_k_x27_2701_ = lean_array_fget_borrowed(v_ks_2676_, v_x_2673_);
v_expr_2702_ = lean_ctor_get(v_k_x27_2701_, 0);
v_configKey_2703_ = lean_ctor_get_uint64(v_k_x27_2701_, sizeof(void*)*1);
v___x_2704_ = lean_expr_equal(v_expr_2699_, v_expr_2702_);
if (v___x_2704_ == 0)
{
v___y_2682_ = v___x_2704_;
goto v___jp_2681_;
}
else
{
uint8_t v___x_2705_; 
v___x_2705_ = lean_uint64_dec_eq(v_configKey_2700_, v_configKey_2703_);
v___y_2682_ = v___x_2705_;
goto v___jp_2681_;
}
}
v___jp_2681_:
{
if (v___y_2682_ == 0)
{
lean_object* v___x_2684_; 
if (v_isShared_2680_ == 0)
{
v___x_2684_ = v___x_2679_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_ks_2676_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_vs_2677_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_x_2673_, v___x_2685_);
lean_dec(v_x_2673_);
v_x_2672_ = v___x_2684_;
v_x_2673_ = v___x_2686_;
goto _start;
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2689_ = lean_array_fset(v_ks_2676_, v_x_2673_, v_x_2674_);
v___x_2690_ = lean_array_fset(v_vs_2677_, v_x_2673_, v_x_2675_);
lean_dec(v_x_2673_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 1, v___x_2690_);
lean_ctor_set(v___x_2679_, 0, v___x_2689_);
v___x_2692_ = v___x_2679_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(lean_object* v_n_2707_, lean_object* v_k_2708_, lean_object* v_v_2709_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2707_, v___x_2710_, v_k_2708_, v_v_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object* v_x_2713_, size_t v_x_2714_, size_t v_x_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
if (lean_obj_tag(v_x_2713_) == 0)
{
lean_object* v_es_2718_; size_t v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; size_t v___x_2722_; lean_object* v_j_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_es_2718_ = lean_ctor_get(v_x_2713_, 0);
v___x_2719_ = ((size_t)5ULL);
v___x_2720_ = ((size_t)1ULL);
v___x_2721_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2722_ = lean_usize_land(v_x_2714_, v___x_2721_);
v_j_2723_ = lean_usize_to_nat(v___x_2722_);
v___x_2724_ = lean_array_get_size(v_es_2718_);
v___x_2725_ = lean_nat_dec_lt(v_j_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_dec(v_j_2723_);
lean_dec(v_x_2717_);
lean_dec_ref(v_x_2716_);
return v_x_2713_;
}
else
{
lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2769_; 
lean_inc_ref(v_es_2718_);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_x_2713_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v_x_2713_, 0);
lean_dec(v_unused_2770_);
v___x_2727_ = v_x_2713_;
v_isShared_2728_ = v_isSharedCheck_2769_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v_x_2713_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2769_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_v_2729_; lean_object* v___x_2730_; lean_object* v_xs_x27_2731_; lean_object* v___y_2733_; 
v_v_2729_ = lean_array_fget(v_es_2718_, v_j_2723_);
v___x_2730_ = lean_box(0);
v_xs_x27_2731_ = lean_array_fset(v_es_2718_, v_j_2723_, v___x_2730_);
switch(lean_obj_tag(v_v_2729_))
{
case 0:
{
lean_object* v_key_2738_; lean_object* v_val_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2756_; 
v_key_2738_ = lean_ctor_get(v_v_2729_, 0);
v_val_2739_ = lean_ctor_get(v_v_2729_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_v_2729_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2741_ = v_v_2729_;
v_isShared_2742_ = v_isSharedCheck_2756_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_val_2739_);
lean_inc(v_key_2738_);
lean_dec(v_v_2729_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2756_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
uint8_t v___y_2744_; lean_object* v_expr_2750_; uint64_t v_configKey_2751_; lean_object* v_expr_2752_; uint64_t v_configKey_2753_; uint8_t v___x_2754_; 
v_expr_2750_ = lean_ctor_get(v_x_2716_, 0);
v_configKey_2751_ = lean_ctor_get_uint64(v_x_2716_, sizeof(void*)*1);
v_expr_2752_ = lean_ctor_get(v_key_2738_, 0);
v_configKey_2753_ = lean_ctor_get_uint64(v_key_2738_, sizeof(void*)*1);
v___x_2754_ = lean_expr_equal(v_expr_2750_, v_expr_2752_);
if (v___x_2754_ == 0)
{
v___y_2744_ = v___x_2754_;
goto v___jp_2743_;
}
else
{
uint8_t v___x_2755_; 
v___x_2755_ = lean_uint64_dec_eq(v_configKey_2751_, v_configKey_2753_);
v___y_2744_ = v___x_2755_;
goto v___jp_2743_;
}
v___jp_2743_:
{
if (v___y_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_del_object(v___x_2741_);
v___x_2745_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2738_, v_val_2739_, v_x_2716_, v_x_2717_);
v___x_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
v___y_2733_ = v___x_2746_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2748_; 
lean_dec(v_val_2739_);
lean_dec(v_key_2738_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v_x_2717_);
lean_ctor_set(v___x_2741_, 0, v_x_2716_);
v___x_2748_ = v___x_2741_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_x_2716_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_x_2717_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
v___y_2733_ = v___x_2748_;
goto v___jp_2732_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2767_; 
v_node_2757_ = lean_ctor_get(v_v_2729_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_v_2729_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2759_ = v_v_2729_;
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_node_2757_);
lean_dec(v_v_2729_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
size_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2761_ = lean_usize_shift_right(v_x_2714_, v___x_2719_);
v___x_2762_ = lean_usize_add(v_x_2715_, v___x_2720_);
v___x_2763_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_node_2757_, v___x_2761_, v___x_2762_, v_x_2716_, v_x_2717_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2763_);
v___x_2765_ = v___x_2759_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v___y_2733_ = v___x_2765_;
goto v___jp_2732_;
}
}
}
default: 
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_x_2716_);
lean_ctor_set(v___x_2768_, 1, v_x_2717_);
v___y_2733_ = v___x_2768_;
goto v___jp_2732_;
}
}
v___jp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_array_fset(v_xs_x27_2731_, v_j_2723_, v___y_2733_);
lean_dec(v_j_2723_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2734_);
v___x_2736_ = v___x_2727_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
else
{
lean_object* v_ks_2771_; lean_object* v_vs_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2792_; 
v_ks_2771_ = lean_ctor_get(v_x_2713_, 0);
v_vs_2772_ = lean_ctor_get(v_x_2713_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_x_2713_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2774_ = v_x_2713_;
v_isShared_2775_ = v_isSharedCheck_2792_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_vs_2772_);
lean_inc(v_ks_2771_);
lean_dec(v_x_2713_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2792_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_ks_2771_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_vs_2772_);
v___x_2777_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v_newNode_2778_; uint8_t v___y_2780_; size_t v___x_2786_; uint8_t v___x_2787_; 
v_newNode_2778_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v___x_2777_, v_x_2716_, v_x_2717_);
v___x_2786_ = ((size_t)7ULL);
v___x_2787_ = lean_usize_dec_le(v___x_2786_, v_x_2715_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2788_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2778_);
v___x_2789_ = lean_unsigned_to_nat(4u);
v___x_2790_ = lean_nat_dec_lt(v___x_2788_, v___x_2789_);
lean_dec(v___x_2788_);
v___y_2780_ = v___x_2790_;
goto v___jp_2779_;
}
else
{
v___y_2780_ = v___x_2787_;
goto v___jp_2779_;
}
v___jp_2779_:
{
if (v___y_2780_ == 0)
{
lean_object* v_ks_2781_; lean_object* v_vs_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_ks_2781_ = lean_ctor_get(v_newNode_2778_, 0);
lean_inc_ref(v_ks_2781_);
v_vs_2782_ = lean_ctor_get(v_newNode_2778_, 1);
lean_inc_ref(v_vs_2782_);
lean_dec_ref(v_newNode_2778_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0);
v___x_2785_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_x_2715_, v_ks_2781_, v_vs_2782_, v___x_2783_, v___x_2784_);
lean_dec_ref(v_vs_2782_);
lean_dec_ref(v_ks_2781_);
return v___x_2785_;
}
else
{
return v_newNode_2778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(size_t v_depth_2793_, lean_object* v_keys_2794_, lean_object* v_vals_2795_, lean_object* v_i_2796_, lean_object* v_entries_2797_){
_start:
{
lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2798_ = lean_array_get_size(v_keys_2794_);
v___x_2799_ = lean_nat_dec_lt(v_i_2796_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_dec(v_i_2796_);
return v_entries_2797_;
}
else
{
lean_object* v_k_2800_; lean_object* v_expr_2801_; uint64_t v_configKey_2802_; lean_object* v_v_2803_; uint64_t v___x_2804_; uint64_t v___x_2805_; size_t v_h_2806_; size_t v___x_2807_; lean_object* v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; size_t v_h_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_k_2800_ = lean_array_fget_borrowed(v_keys_2794_, v_i_2796_);
v_expr_2801_ = lean_ctor_get(v_k_2800_, 0);
v_configKey_2802_ = lean_ctor_get_uint64(v_k_2800_, sizeof(void*)*1);
v_v_2803_ = lean_array_fget_borrowed(v_vals_2795_, v_i_2796_);
v___x_2804_ = l_Lean_Expr_hash(v_expr_2801_);
v___x_2805_ = lean_uint64_mix_hash(v___x_2804_, v_configKey_2802_);
v_h_2806_ = lean_uint64_to_usize(v___x_2805_);
v___x_2807_ = ((size_t)5ULL);
v___x_2808_ = lean_unsigned_to_nat(1u);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_sub(v_depth_2793_, v___x_2809_);
v___x_2811_ = lean_usize_mul(v___x_2807_, v___x_2810_);
v_h_2812_ = lean_usize_shift_right(v_h_2806_, v___x_2811_);
v___x_2813_ = lean_nat_add(v_i_2796_, v___x_2808_);
lean_dec(v_i_2796_);
lean_inc(v_v_2803_);
lean_inc(v_k_2800_);
v___x_2814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_entries_2797_, v_h_2812_, v_depth_2793_, v_k_2800_, v_v_2803_);
v_i_2796_ = v___x_2813_;
v_entries_2797_ = v___x_2814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_2816_, lean_object* v_keys_2817_, lean_object* v_vals_2818_, lean_object* v_i_2819_, lean_object* v_entries_2820_){
_start:
{
size_t v_depth_boxed_2821_; lean_object* v_res_2822_; 
v_depth_boxed_2821_ = lean_unbox_usize(v_depth_2816_);
lean_dec(v_depth_2816_);
v_res_2822_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2821_, v_keys_2817_, v_vals_2818_, v_i_2819_, v_entries_2820_);
lean_dec_ref(v_vals_2818_);
lean_dec_ref(v_keys_2817_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object* v_x_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_){
_start:
{
size_t v_x_2105__boxed_2828_; size_t v_x_2106__boxed_2829_; lean_object* v_res_2830_; 
v_x_2105__boxed_2828_ = lean_unbox_usize(v_x_2824_);
lean_dec(v_x_2824_);
v_x_2106__boxed_2829_ = lean_unbox_usize(v_x_2825_);
lean_dec(v_x_2825_);
v_res_2830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2823_, v_x_2105__boxed_2828_, v_x_2106__boxed_2829_, v_x_2826_, v_x_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_){
_start:
{
lean_object* v_expr_2834_; uint64_t v_configKey_2835_; uint64_t v___x_2836_; uint64_t v___x_2837_; size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v_expr_2834_ = lean_ctor_get(v_x_2832_, 0);
v_configKey_2835_ = lean_ctor_get_uint64(v_x_2832_, sizeof(void*)*1);
v___x_2836_ = l_Lean_Expr_hash(v_expr_2834_);
v___x_2837_ = lean_uint64_mix_hash(v___x_2836_, v_configKey_2835_);
v___x_2838_ = lean_uint64_to_usize(v___x_2837_);
v___x_2839_ = ((size_t)1ULL);
v___x_2840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2831_, v___x_2838_, v___x_2839_, v_x_2832_, v_x_2833_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2841_, lean_object* v_vals_2842_, lean_object* v_i_2843_, lean_object* v_k_2844_){
_start:
{
uint8_t v___y_2846_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = lean_array_get_size(v_keys_2841_);
v___x_2853_ = lean_nat_dec_lt(v_i_2843_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec(v_i_2843_);
v___x_2854_ = lean_box(0);
return v___x_2854_;
}
else
{
lean_object* v_expr_2855_; uint64_t v_configKey_2856_; lean_object* v_k_x27_2857_; lean_object* v_expr_2858_; uint64_t v_configKey_2859_; uint8_t v___x_2860_; 
v_expr_2855_ = lean_ctor_get(v_k_2844_, 0);
v_configKey_2856_ = lean_ctor_get_uint64(v_k_2844_, sizeof(void*)*1);
v_k_x27_2857_ = lean_array_fget_borrowed(v_keys_2841_, v_i_2843_);
v_expr_2858_ = lean_ctor_get(v_k_x27_2857_, 0);
v_configKey_2859_ = lean_ctor_get_uint64(v_k_x27_2857_, sizeof(void*)*1);
v___x_2860_ = lean_expr_equal(v_expr_2855_, v_expr_2858_);
if (v___x_2860_ == 0)
{
v___y_2846_ = v___x_2860_;
goto v___jp_2845_;
}
else
{
uint8_t v___x_2861_; 
v___x_2861_ = lean_uint64_dec_eq(v_configKey_2856_, v_configKey_2859_);
v___y_2846_ = v___x_2861_;
goto v___jp_2845_;
}
}
v___jp_2845_:
{
if (v___y_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = lean_nat_add(v_i_2843_, v___x_2847_);
lean_dec(v_i_2843_);
v_i_2843_ = v___x_2848_;
goto _start;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_array_fget_borrowed(v_vals_2842_, v_i_2843_);
lean_dec(v_i_2843_);
lean_inc(v___x_2850_);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2862_, lean_object* v_vals_2863_, lean_object* v_i_2864_, lean_object* v_k_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_2862_, v_vals_2863_, v_i_2864_, v_k_2865_);
lean_dec_ref(v_k_2865_);
lean_dec_ref(v_vals_2863_);
lean_dec_ref(v_keys_2862_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object* v_x_2867_, size_t v_x_2868_, lean_object* v_x_2869_){
_start:
{
if (lean_obj_tag(v_x_2867_) == 0)
{
lean_object* v_es_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2898_; 
v_es_2870_ = lean_ctor_get(v_x_2867_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_x_2867_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2872_ = v_x_2867_;
v_isShared_2873_ = v_isSharedCheck_2898_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_es_2870_);
lean_dec(v_x_2867_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2898_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; size_t v___x_2875_; size_t v___x_2876_; size_t v___x_2877_; lean_object* v_j_2878_; lean_object* v___x_2879_; 
v___x_2874_ = lean_box(2);
v___x_2875_ = ((size_t)5ULL);
v___x_2876_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2877_ = lean_usize_land(v_x_2868_, v___x_2876_);
v_j_2878_ = lean_usize_to_nat(v___x_2877_);
v___x_2879_ = lean_array_get(v___x_2874_, v_es_2870_, v_j_2878_);
lean_dec(v_j_2878_);
lean_dec_ref(v_es_2870_);
switch(lean_obj_tag(v___x_2879_))
{
case 0:
{
lean_object* v_key_2880_; lean_object* v_val_2881_; uint8_t v___y_2883_; lean_object* v_expr_2888_; uint64_t v_configKey_2889_; lean_object* v_expr_2890_; uint64_t v_configKey_2891_; uint8_t v___x_2892_; 
v_key_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_key_2880_);
v_val_2881_ = lean_ctor_get(v___x_2879_, 1);
lean_inc(v_val_2881_);
lean_dec_ref(v___x_2879_);
v_expr_2888_ = lean_ctor_get(v_x_2869_, 0);
v_configKey_2889_ = lean_ctor_get_uint64(v_x_2869_, sizeof(void*)*1);
v_expr_2890_ = lean_ctor_get(v_key_2880_, 0);
lean_inc_ref(v_expr_2890_);
v_configKey_2891_ = lean_ctor_get_uint64(v_key_2880_, sizeof(void*)*1);
lean_dec(v_key_2880_);
v___x_2892_ = lean_expr_equal(v_expr_2888_, v_expr_2890_);
lean_dec_ref(v_expr_2890_);
if (v___x_2892_ == 0)
{
v___y_2883_ = v___x_2892_;
goto v___jp_2882_;
}
else
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_uint64_dec_eq(v_configKey_2889_, v_configKey_2891_);
v___y_2883_ = v___x_2893_;
goto v___jp_2882_;
}
v___jp_2882_:
{
if (v___y_2883_ == 0)
{
lean_object* v___x_2884_; 
lean_dec(v_val_2881_);
lean_del_object(v___x_2872_);
v___x_2884_ = lean_box(0);
return v___x_2884_;
}
else
{
lean_object* v___x_2886_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 1);
lean_ctor_set(v___x_2872_, 0, v_val_2881_);
v___x_2886_ = v___x_2872_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_val_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
case 1:
{
lean_object* v_node_2894_; size_t v___x_2895_; 
lean_del_object(v___x_2872_);
v_node_2894_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_node_2894_);
lean_dec_ref(v___x_2879_);
v___x_2895_ = lean_usize_shift_right(v_x_2868_, v___x_2875_);
v_x_2867_ = v_node_2894_;
v_x_2868_ = v___x_2895_;
goto _start;
}
default: 
{
lean_object* v___x_2897_; 
lean_del_object(v___x_2872_);
v___x_2897_ = lean_box(0);
return v___x_2897_;
}
}
}
}
else
{
lean_object* v_ks_2899_; lean_object* v_vs_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_ks_2899_ = lean_ctor_get(v_x_2867_, 0);
lean_inc_ref(v_ks_2899_);
v_vs_2900_ = lean_ctor_get(v_x_2867_, 1);
lean_inc_ref(v_vs_2900_);
lean_dec_ref(v_x_2867_);
v___x_2901_ = lean_unsigned_to_nat(0u);
v___x_2902_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_ks_2899_, v_vs_2900_, v___x_2901_, v_x_2869_);
lean_dec_ref(v_vs_2900_);
lean_dec_ref(v_ks_2899_);
return v___x_2902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_){
_start:
{
size_t v_x_2320__boxed_2906_; lean_object* v_res_2907_; 
v_x_2320__boxed_2906_ = lean_unbox_usize(v_x_2904_);
lean_dec(v_x_2904_);
v_res_2907_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2903_, v_x_2320__boxed_2906_, v_x_2905_);
lean_dec_ref(v_x_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object* v_x_2908_, lean_object* v_x_2909_){
_start:
{
lean_object* v_expr_2910_; uint64_t v_configKey_2911_; uint64_t v___x_2912_; uint64_t v___x_2913_; size_t v___x_2914_; lean_object* v___x_2915_; 
v_expr_2910_ = lean_ctor_get(v_x_2909_, 0);
v_configKey_2911_ = lean_ctor_get_uint64(v_x_2909_, sizeof(void*)*1);
v___x_2912_ = l_Lean_Expr_hash(v_expr_2910_);
v___x_2913_ = lean_uint64_mix_hash(v___x_2912_, v_configKey_2911_);
v___x_2914_ = lean_uint64_to_usize(v___x_2913_);
v___x_2915_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2908_, v___x_2914_, v_x_2909_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_2916_, v_x_2917_);
lean_dec_ref(v_x_2917_);
return v_res_2918_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_2921_ = l_Lean_stringToMessageData(v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
switch(lean_obj_tag(v_e_2922_))
{
case 0:
{
lean_object* v_deBruijnIndex_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_deBruijnIndex_2928_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_deBruijnIndex_2928_);
lean_dec_ref(v_e_2922_);
v___x_2929_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_2930_ = l_Lean_mkBVar(v_deBruijnIndex_2928_);
v___x_2931_ = l_Lean_MessageData_ofExpr(v___x_2930_);
v___x_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2929_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2932_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_2933_;
}
case 1:
{
lean_object* v_fvarId_2934_; lean_object* v___x_2935_; 
v_fvarId_2934_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_fvarId_2934_);
lean_dec_ref(v_e_2922_);
v___x_2935_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2934_, v_a_2923_, v_a_2925_, v_a_2926_);
return v___x_2935_;
}
case 2:
{
lean_object* v_mvarId_2936_; lean_object* v___x_2937_; 
v_mvarId_2936_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_mvarId_2936_);
lean_dec_ref(v_e_2922_);
v___x_2937_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2936_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_2937_;
}
case 3:
{
lean_object* v_u_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec_ref(v_a_2923_);
v_u_2938_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_u_2938_);
lean_dec_ref(v_e_2922_);
v___x_2939_ = l_Lean_Level_succ___override(v_u_2938_);
v___x_2940_ = l_Lean_mkSort(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
case 4:
{
lean_object* v_us_2942_; 
v_us_2942_ = lean_ctor_get(v_e_2922_, 1);
lean_inc(v_us_2942_);
if (lean_obj_tag(v_us_2942_) == 0)
{
lean_object* v_declName_2943_; lean_object* v___x_2944_; 
v_declName_2943_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_declName_2943_);
lean_dec_ref(v_e_2922_);
v___x_2944_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2943_, v_us_2942_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_2944_;
}
else
{
uint8_t v_cacheInferType_2945_; 
v_cacheInferType_2945_ = lean_ctor_get_uint8(v_a_2923_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2945_ == 0)
{
lean_object* v_declName_2946_; lean_object* v___x_2947_; 
v_declName_2946_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_declName_2946_);
lean_dec_ref(v_e_2922_);
v___x_2947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2946_, v_us_2942_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_2947_;
}
else
{
lean_object* v_declName_2948_; uint8_t v___x_2949_; 
v_declName_2948_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_declName_2948_);
v___x_2949_ = l_Lean_Expr_hasMVar(v_e_2922_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3002_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_3002_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3002_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v_cache_2956_; lean_object* v_inferType_2957_; lean_object* v___x_2958_; 
v___x_2955_ = lean_st_ref_get(v_a_2924_);
v_cache_2956_ = lean_ctor_get(v___x_2955_, 1);
lean_inc_ref(v_cache_2956_);
lean_dec(v___x_2955_);
v_inferType_2957_ = lean_ctor_get(v_cache_2956_, 0);
lean_inc_ref(v_inferType_2957_);
lean_dec_ref(v_cache_2956_);
v___x_2958_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_2957_, v_a_2951_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; 
lean_del_object(v___x_2953_);
v___x_2959_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2948_, v_us_2942_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; uint8_t v___x_2961_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
v___x_2961_ = l_Lean_Expr_hasMVar(v_a_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2996_; 
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v___x_2959_, 0);
lean_dec(v_unused_2997_);
v___x_2963_ = v___x_2959_;
v_isShared_2964_ = v_isSharedCheck_2996_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v___x_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2996_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v_cache_2966_; lean_object* v_mctx_2967_; lean_object* v_zetaDeltaFVarIds_2968_; lean_object* v_postponed_2969_; lean_object* v_diag_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2995_; 
v___x_2965_ = lean_st_ref_take(v_a_2924_);
v_cache_2966_ = lean_ctor_get(v___x_2965_, 1);
v_mctx_2967_ = lean_ctor_get(v___x_2965_, 0);
v_zetaDeltaFVarIds_2968_ = lean_ctor_get(v___x_2965_, 2);
v_postponed_2969_ = lean_ctor_get(v___x_2965_, 3);
v_diag_2970_ = lean_ctor_get(v___x_2965_, 4);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2972_ = v___x_2965_;
v_isShared_2973_ = v_isSharedCheck_2995_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_diag_2970_);
lean_inc(v_postponed_2969_);
lean_inc(v_zetaDeltaFVarIds_2968_);
lean_inc(v_cache_2966_);
lean_inc(v_mctx_2967_);
lean_dec(v___x_2965_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2995_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_inferType_2974_; lean_object* v_funInfo_2975_; lean_object* v_synthInstance_2976_; lean_object* v_whnf_2977_; lean_object* v_defEqTrans_2978_; lean_object* v_defEqPerm_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2994_; 
v_inferType_2974_ = lean_ctor_get(v_cache_2966_, 0);
v_funInfo_2975_ = lean_ctor_get(v_cache_2966_, 1);
v_synthInstance_2976_ = lean_ctor_get(v_cache_2966_, 2);
v_whnf_2977_ = lean_ctor_get(v_cache_2966_, 3);
v_defEqTrans_2978_ = lean_ctor_get(v_cache_2966_, 4);
v_defEqPerm_2979_ = lean_ctor_get(v_cache_2966_, 5);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_cache_2966_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2981_ = v_cache_2966_;
v_isShared_2982_ = v_isSharedCheck_2994_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_defEqPerm_2979_);
lean_inc(v_defEqTrans_2978_);
lean_inc(v_whnf_2977_);
lean_inc(v_synthInstance_2976_);
lean_inc(v_funInfo_2975_);
lean_inc(v_inferType_2974_);
lean_dec(v_cache_2966_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2994_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
lean_inc(v_a_2960_);
v___x_2983_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_2974_, v_a_2951_, v_a_2960_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_funInfo_2975_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_synthInstance_2976_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_whnf_2977_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_defEqTrans_2978_);
lean_ctor_set(v_reuseFailAlloc_2993_, 5, v_defEqPerm_2979_);
v___x_2985_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2987_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 1, v___x_2985_);
v___x_2987_ = v___x_2972_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_mctx_2967_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_zetaDeltaFVarIds_2968_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_postponed_2969_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v_diag_2970_);
v___x_2987_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_st_ref_set(v_a_2924_, v___x_2987_);
if (v_isShared_2964_ == 0)
{
v___x_2990_ = v___x_2963_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2960_);
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
}
}
}
else
{
lean_dec(v_a_2960_);
lean_dec(v_a_2951_);
return v___x_2959_;
}
}
else
{
lean_dec(v_a_2951_);
return v___x_2959_;
}
}
else
{
lean_object* v_val_2998_; lean_object* v___x_3000_; 
lean_dec(v_a_2951_);
lean_dec(v_declName_2948_);
lean_dec(v_us_2942_);
lean_dec_ref(v_a_2923_);
v_val_2998_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_val_2998_);
lean_dec_ref(v___x_2958_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v_val_2998_);
v___x_3000_ = v___x_2953_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_val_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_declName_2948_);
lean_dec(v_us_2942_);
lean_dec_ref(v_a_2923_);
v_a_3003_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2950_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2950_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v___x_3011_; 
lean_dec_ref(v_e_2922_);
v___x_3011_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2948_, v_us_2942_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3011_;
}
}
}
}
case 5:
{
lean_object* v_fn_3012_; uint8_t v_cacheInferType_3013_; lean_object* v_nargs_3014_; lean_object* v___x_3015_; lean_object* v_dummy_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_fn_3012_ = lean_ctor_get(v_e_2922_, 0);
v_cacheInferType_3013_ = lean_ctor_get_uint8(v_a_2923_, sizeof(void*)*7 + 3);
v_nargs_3014_ = l_Lean_Expr_getAppNumArgs(v_e_2922_);
v___x_3015_ = l_Lean_Expr_getAppFn(v_fn_3012_);
v_dummy_3016_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3014_);
v___x_3017_ = lean_mk_array(v_nargs_3014_, v_dummy_3016_);
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_sub(v_nargs_3014_, v___x_3018_);
lean_dec(v_nargs_3014_);
lean_inc_ref(v_e_2922_);
v___x_3020_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2922_, v___x_3017_, v___x_3019_);
if (v_cacheInferType_3013_ == 0)
{
lean_object* v___x_3021_; 
lean_dec_ref(v_e_2922_);
v___x_3021_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3015_, v___x_3020_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
lean_dec_ref(v___x_3020_);
return v___x_3021_;
}
else
{
uint8_t v___x_3022_; 
v___x_3022_ = l_Lean_Expr_hasMVar(v_e_2922_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2922_, v_a_2923_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3075_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3075_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3075_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v_cache_3029_; lean_object* v_inferType_3030_; lean_object* v___x_3031_; 
v___x_3028_ = lean_st_ref_get(v_a_2924_);
v_cache_3029_ = lean_ctor_get(v___x_3028_, 1);
lean_inc_ref(v_cache_3029_);
lean_dec(v___x_3028_);
v_inferType_3030_ = lean_ctor_get(v_cache_3029_, 0);
lean_inc_ref(v_inferType_3030_);
lean_dec_ref(v_cache_3029_);
v___x_3031_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3030_, v_a_3024_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3032_; 
lean_del_object(v___x_3026_);
v___x_3032_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3015_, v___x_3020_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
lean_dec_ref(v___x_3020_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
v___x_3034_ = l_Lean_Expr_hasMVar(v_a_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3069_; 
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v___x_3032_, 0);
lean_dec(v_unused_3070_);
v___x_3036_ = v___x_3032_;
v_isShared_3037_ = v_isSharedCheck_3069_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3032_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3069_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v_cache_3039_; lean_object* v_mctx_3040_; lean_object* v_zetaDeltaFVarIds_3041_; lean_object* v_postponed_3042_; lean_object* v_diag_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3068_; 
v___x_3038_ = lean_st_ref_take(v_a_2924_);
v_cache_3039_ = lean_ctor_get(v___x_3038_, 1);
v_mctx_3040_ = lean_ctor_get(v___x_3038_, 0);
v_zetaDeltaFVarIds_3041_ = lean_ctor_get(v___x_3038_, 2);
v_postponed_3042_ = lean_ctor_get(v___x_3038_, 3);
v_diag_3043_ = lean_ctor_get(v___x_3038_, 4);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3045_ = v___x_3038_;
v_isShared_3046_ = v_isSharedCheck_3068_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_diag_3043_);
lean_inc(v_postponed_3042_);
lean_inc(v_zetaDeltaFVarIds_3041_);
lean_inc(v_cache_3039_);
lean_inc(v_mctx_3040_);
lean_dec(v___x_3038_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3068_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_inferType_3047_; lean_object* v_funInfo_3048_; lean_object* v_synthInstance_3049_; lean_object* v_whnf_3050_; lean_object* v_defEqTrans_3051_; lean_object* v_defEqPerm_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3067_; 
v_inferType_3047_ = lean_ctor_get(v_cache_3039_, 0);
v_funInfo_3048_ = lean_ctor_get(v_cache_3039_, 1);
v_synthInstance_3049_ = lean_ctor_get(v_cache_3039_, 2);
v_whnf_3050_ = lean_ctor_get(v_cache_3039_, 3);
v_defEqTrans_3051_ = lean_ctor_get(v_cache_3039_, 4);
v_defEqPerm_3052_ = lean_ctor_get(v_cache_3039_, 5);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_cache_3039_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3054_ = v_cache_3039_;
v_isShared_3055_ = v_isSharedCheck_3067_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_defEqPerm_3052_);
lean_inc(v_defEqTrans_3051_);
lean_inc(v_whnf_3050_);
lean_inc(v_synthInstance_3049_);
lean_inc(v_funInfo_3048_);
lean_inc(v_inferType_3047_);
lean_dec(v_cache_3039_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3067_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
lean_inc(v_a_3033_);
v___x_3056_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3047_, v_a_3024_, v_a_3033_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_funInfo_3048_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v_synthInstance_3049_);
lean_ctor_set(v_reuseFailAlloc_3066_, 3, v_whnf_3050_);
lean_ctor_set(v_reuseFailAlloc_3066_, 4, v_defEqTrans_3051_);
lean_ctor_set(v_reuseFailAlloc_3066_, 5, v_defEqPerm_3052_);
v___x_3058_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 1, v___x_3058_);
v___x_3060_ = v___x_3045_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_mctx_3040_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_zetaDeltaFVarIds_3041_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_postponed_3042_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_diag_3043_);
v___x_3060_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = lean_st_ref_set(v_a_2924_, v___x_3060_);
if (v_isShared_3037_ == 0)
{
v___x_3063_ = v___x_3036_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3033_);
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
}
}
}
else
{
lean_dec(v_a_3033_);
lean_dec(v_a_3024_);
return v___x_3032_;
}
}
else
{
lean_dec(v_a_3024_);
return v___x_3032_;
}
}
else
{
lean_object* v_val_3071_; lean_object* v___x_3073_; 
lean_dec(v_a_3024_);
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___x_3015_);
lean_dec_ref(v_a_2923_);
v_val_3071_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_val_3071_);
lean_dec_ref(v___x_3031_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_val_3071_);
v___x_3073_ = v___x_3026_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_val_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___x_3015_);
lean_dec_ref(v_a_2923_);
v_a_3076_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3023_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3023_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v___x_3084_; 
lean_dec_ref(v_e_2922_);
v___x_3084_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3015_, v___x_3020_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
lean_dec_ref(v___x_3020_);
return v___x_3084_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3085_; 
v_cacheInferType_3085_ = lean_ctor_get_uint8(v_a_2923_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3086_;
}
else
{
uint8_t v___x_3087_; 
v___x_3087_ = l_Lean_Expr_hasMVar(v_e_2922_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
lean_inc_ref(v_e_2922_);
v___x_3088_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2922_, v_a_2923_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3140_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3140_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3140_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v_cache_3094_; lean_object* v_inferType_3095_; lean_object* v___x_3096_; 
v___x_3093_ = lean_st_ref_get(v_a_2924_);
v_cache_3094_ = lean_ctor_get(v___x_3093_, 1);
lean_inc_ref(v_cache_3094_);
lean_dec(v___x_3093_);
v_inferType_3095_ = lean_ctor_get(v_cache_3094_, 0);
lean_inc_ref(v_inferType_3095_);
lean_dec_ref(v_cache_3094_);
v___x_3096_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3095_, v_a_3089_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v___x_3097_; 
lean_del_object(v___x_3091_);
v___x_3097_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; uint8_t v___x_3099_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
v___x_3099_ = l_Lean_Expr_hasMVar(v_a_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3134_; 
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3097_, 0);
lean_dec(v_unused_3135_);
v___x_3101_ = v___x_3097_;
v_isShared_3102_ = v_isSharedCheck_3134_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v___x_3097_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3134_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v_cache_3104_; lean_object* v_mctx_3105_; lean_object* v_zetaDeltaFVarIds_3106_; lean_object* v_postponed_3107_; lean_object* v_diag_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3133_; 
v___x_3103_ = lean_st_ref_take(v_a_2924_);
v_cache_3104_ = lean_ctor_get(v___x_3103_, 1);
v_mctx_3105_ = lean_ctor_get(v___x_3103_, 0);
v_zetaDeltaFVarIds_3106_ = lean_ctor_get(v___x_3103_, 2);
v_postponed_3107_ = lean_ctor_get(v___x_3103_, 3);
v_diag_3108_ = lean_ctor_get(v___x_3103_, 4);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3110_ = v___x_3103_;
v_isShared_3111_ = v_isSharedCheck_3133_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_diag_3108_);
lean_inc(v_postponed_3107_);
lean_inc(v_zetaDeltaFVarIds_3106_);
lean_inc(v_cache_3104_);
lean_inc(v_mctx_3105_);
lean_dec(v___x_3103_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3133_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_inferType_3112_; lean_object* v_funInfo_3113_; lean_object* v_synthInstance_3114_; lean_object* v_whnf_3115_; lean_object* v_defEqTrans_3116_; lean_object* v_defEqPerm_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3132_; 
v_inferType_3112_ = lean_ctor_get(v_cache_3104_, 0);
v_funInfo_3113_ = lean_ctor_get(v_cache_3104_, 1);
v_synthInstance_3114_ = lean_ctor_get(v_cache_3104_, 2);
v_whnf_3115_ = lean_ctor_get(v_cache_3104_, 3);
v_defEqTrans_3116_ = lean_ctor_get(v_cache_3104_, 4);
v_defEqPerm_3117_ = lean_ctor_get(v_cache_3104_, 5);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_cache_3104_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3119_ = v_cache_3104_;
v_isShared_3120_ = v_isSharedCheck_3132_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_defEqPerm_3117_);
lean_inc(v_defEqTrans_3116_);
lean_inc(v_whnf_3115_);
lean_inc(v_synthInstance_3114_);
lean_inc(v_funInfo_3113_);
lean_inc(v_inferType_3112_);
lean_dec(v_cache_3104_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3132_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
lean_inc(v_a_3098_);
v___x_3121_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3112_, v_a_3089_, v_a_3098_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3121_);
v___x_3123_ = v___x_3119_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_funInfo_3113_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_synthInstance_3114_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_whnf_3115_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_defEqTrans_3116_);
lean_ctor_set(v_reuseFailAlloc_3131_, 5, v_defEqPerm_3117_);
v___x_3123_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3125_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v___x_3123_);
v___x_3125_ = v___x_3110_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_mctx_3105_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_zetaDeltaFVarIds_3106_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_postponed_3107_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_diag_3108_);
v___x_3125_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_st_ref_set(v_a_2924_, v___x_3125_);
if (v_isShared_3102_ == 0)
{
v___x_3128_ = v___x_3101_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3098_);
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
}
}
}
else
{
lean_dec(v_a_3098_);
lean_dec(v_a_3089_);
return v___x_3097_;
}
}
else
{
lean_dec(v_a_3089_);
return v___x_3097_;
}
}
else
{
lean_object* v_val_3136_; lean_object* v___x_3138_; 
lean_dec(v_a_3089_);
lean_dec_ref(v_e_2922_);
lean_dec_ref(v_a_2923_);
v_val_3136_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3136_);
lean_dec_ref(v___x_3096_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v_val_3136_);
v___x_3138_ = v___x_3091_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_val_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_e_2922_);
lean_dec_ref(v_a_2923_);
v_a_3141_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3088_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3088_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3149_;
}
}
}
case 9:
{
lean_object* v_a_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec_ref(v_a_2923_);
v_a_3150_ = lean_ctor_get(v_e_2922_, 0);
lean_inc_ref(v_a_3150_);
lean_dec_ref(v_e_2922_);
v___x_3151_ = l_Lean_Literal_type(v_a_3150_);
lean_dec_ref(v_a_3150_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
case 10:
{
lean_object* v_expr_3153_; 
v_expr_3153_ = lean_ctor_get(v_e_2922_, 1);
lean_inc_ref(v_expr_3153_);
lean_dec_ref(v_e_2922_);
v_e_2922_ = v_expr_3153_;
goto _start;
}
case 11:
{
uint8_t v_cacheInferType_3155_; 
v_cacheInferType_3155_ = lean_ctor_get_uint8(v_a_2923_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3155_ == 0)
{
lean_object* v_typeName_3156_; lean_object* v_idx_3157_; lean_object* v_struct_3158_; lean_object* v___x_3159_; 
v_typeName_3156_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_typeName_3156_);
v_idx_3157_ = lean_ctor_get(v_e_2922_, 1);
lean_inc(v_idx_3157_);
v_struct_3158_ = lean_ctor_get(v_e_2922_, 2);
lean_inc_ref(v_struct_3158_);
lean_dec_ref(v_e_2922_);
v___x_3159_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3156_, v_idx_3157_, v_struct_3158_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3159_;
}
else
{
lean_object* v_typeName_3160_; lean_object* v_idx_3161_; lean_object* v_struct_3162_; uint8_t v___x_3163_; 
v_typeName_3160_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_typeName_3160_);
v_idx_3161_ = lean_ctor_get(v_e_2922_, 1);
lean_inc(v_idx_3161_);
v_struct_3162_ = lean_ctor_get(v_e_2922_, 2);
lean_inc_ref(v_struct_3162_);
v___x_3163_ = l_Lean_Expr_hasMVar(v_e_2922_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2922_, v_a_2923_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3216_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3216_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3216_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v_cache_3170_; lean_object* v_inferType_3171_; lean_object* v___x_3172_; 
v___x_3169_ = lean_st_ref_get(v_a_2924_);
v_cache_3170_ = lean_ctor_get(v___x_3169_, 1);
lean_inc_ref(v_cache_3170_);
lean_dec(v___x_3169_);
v_inferType_3171_ = lean_ctor_get(v_cache_3170_, 0);
lean_inc_ref(v_inferType_3171_);
lean_dec_ref(v_cache_3170_);
v___x_3172_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3171_, v_a_3165_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3173_; 
lean_del_object(v___x_3167_);
v___x_3173_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3160_, v_idx_3161_, v_struct_3162_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; uint8_t v___x_3175_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
v___x_3175_ = l_Lean_Expr_hasMVar(v_a_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3210_; 
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
v___x_3179_ = lean_st_ref_take(v_a_2924_);
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
v___x_3197_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3188_, v_a_3165_, v_a_3174_);
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
v___x_3202_ = lean_st_ref_set(v_a_2924_, v___x_3201_);
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
lean_dec(v_a_3174_);
lean_dec(v_a_3165_);
return v___x_3173_;
}
}
else
{
lean_dec(v_a_3165_);
return v___x_3173_;
}
}
else
{
lean_object* v_val_3212_; lean_object* v___x_3214_; 
lean_dec(v_a_3165_);
lean_dec_ref(v_struct_3162_);
lean_dec(v_idx_3161_);
lean_dec(v_typeName_3160_);
lean_dec_ref(v_a_2923_);
v_val_3212_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_val_3212_);
lean_dec_ref(v___x_3172_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_val_3212_);
v___x_3214_ = v___x_3167_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_val_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v_struct_3162_);
lean_dec(v_idx_3161_);
lean_dec(v_typeName_3160_);
lean_dec_ref(v_a_2923_);
v_a_3217_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3164_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3164_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v___x_3225_; 
lean_dec_ref(v_e_2922_);
v___x_3225_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3160_, v_idx_3161_, v_struct_3162_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3225_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3226_; 
v_cacheInferType_3226_ = lean_ctor_get_uint8(v_a_2923_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3226_ == 0)
{
lean_object* v___x_3227_; 
v___x_3227_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3227_;
}
else
{
uint8_t v___x_3228_; 
v___x_3228_ = l_Lean_Expr_hasMVar(v_e_2922_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_inc_ref(v_e_2922_);
v___x_3229_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2922_, v_a_2923_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3281_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3281_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3281_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v_cache_3235_; lean_object* v_inferType_3236_; lean_object* v___x_3237_; 
v___x_3234_ = lean_st_ref_get(v_a_2924_);
v_cache_3235_ = lean_ctor_get(v___x_3234_, 1);
lean_inc_ref(v_cache_3235_);
lean_dec(v___x_3234_);
v_inferType_3236_ = lean_ctor_get(v_cache_3235_, 0);
lean_inc_ref(v_inferType_3236_);
lean_dec_ref(v_cache_3235_);
v___x_3237_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3236_, v_a_3230_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3238_; 
lean_del_object(v___x_3232_);
v___x_3238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; uint8_t v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
v___x_3240_ = l_Lean_Expr_hasMVar(v_a_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3275_; 
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
v___x_3244_ = lean_st_ref_take(v_a_2924_);
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
v___x_3262_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3253_, v_a_3230_, v_a_3239_);
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
v___x_3267_ = lean_st_ref_set(v_a_2924_, v___x_3266_);
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
lean_dec(v_a_3239_);
lean_dec(v_a_3230_);
return v___x_3238_;
}
}
else
{
lean_dec(v_a_3230_);
return v___x_3238_;
}
}
else
{
lean_object* v_val_3277_; lean_object* v___x_3279_; 
lean_dec(v_a_3230_);
lean_dec_ref(v_a_2923_);
lean_dec_ref(v_e_2922_);
v_val_3277_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_val_3277_);
lean_dec_ref(v___x_3237_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v_val_3277_);
v___x_3279_ = v___x_3232_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_val_3277_);
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
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref(v_a_2923_);
lean_dec_ref(v_e_2922_);
v_a_3282_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3229_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3229_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
lean_object* v___x_3290_; 
v___x_3290_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec_ref(v_a_2923_);
return v___x_3290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b2_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_3299_, v_x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b2_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b2_3302_, v_x_3303_, v_x_3304_);
lean_dec_ref(v_x_3304_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3306_, lean_object* v_x_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3307_, v_x_3308_, v_x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, size_t v_x_3313_, lean_object* v_x_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3312_, v_x_3313_, v_x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_){
_start:
{
size_t v_x_3132__boxed_3320_; lean_object* v_res_3321_; 
v_x_3132__boxed_3320_ = lean_unbox_usize(v_x_3318_);
lean_dec(v_x_3318_);
v_res_3321_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(v_00_u03b2_3316_, v_x_3317_, v_x_3132__boxed_3320_, v_x_3319_);
lean_dec_ref(v_x_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object* v_00_u03b2_3322_, lean_object* v_x_3323_, size_t v_x_3324_, size_t v_x_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3323_, v_x_3324_, v_x_3325_, v_x_3326_, v_x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
size_t v_x_3143__boxed_3335_; size_t v_x_3144__boxed_3336_; lean_object* v_res_3337_; 
v_x_3143__boxed_3335_ = lean_unbox_usize(v_x_3331_);
lean_dec(v_x_3331_);
v_x_3144__boxed_3336_ = lean_unbox_usize(v_x_3332_);
lean_dec(v_x_3332_);
v_res_3337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(v_00_u03b2_3329_, v_x_3330_, v_x_3143__boxed_3335_, v_x_3144__boxed_3336_, v_x_3333_, v_x_3334_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3338_, lean_object* v_keys_3339_, lean_object* v_vals_3340_, lean_object* v_heq_3341_, lean_object* v_i_3342_, lean_object* v_k_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_3339_, v_vals_3340_, v_i_3342_, v_k_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3345_, lean_object* v_keys_3346_, lean_object* v_vals_3347_, lean_object* v_heq_3348_, lean_object* v_i_3349_, lean_object* v_k_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(v_00_u03b2_3345_, v_keys_3346_, v_vals_3347_, v_heq_3348_, v_i_3349_, v_k_3350_);
lean_dec_ref(v_k_3350_);
lean_dec_ref(v_vals_3347_);
lean_dec_ref(v_keys_3346_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3352_, lean_object* v_n_3353_, lean_object* v_k_3354_, lean_object* v_v_3355_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v_n_3353_, v_k_3354_, v_v_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3357_, size_t v_depth_3358_, lean_object* v_keys_3359_, lean_object* v_vals_3360_, lean_object* v_heq_3361_, lean_object* v_i_3362_, lean_object* v_entries_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_3358_, v_keys_3359_, v_vals_3360_, v_i_3362_, v_entries_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3365_, lean_object* v_depth_3366_, lean_object* v_keys_3367_, lean_object* v_vals_3368_, lean_object* v_heq_3369_, lean_object* v_i_3370_, lean_object* v_entries_3371_){
_start:
{
size_t v_depth_boxed_3372_; lean_object* v_res_3373_; 
v_depth_boxed_3372_ = lean_unbox_usize(v_depth_3366_);
lean_dec(v_depth_3366_);
v_res_3373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(v_00_u03b2_3365_, v_depth_boxed_3372_, v_keys_3367_, v_vals_3368_, v_heq_3369_, v_i_3370_, v_entries_3371_);
lean_dec_ref(v_vals_3368_);
lean_dec_ref(v_keys_3367_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3374_, lean_object* v_x_3375_, lean_object* v_x_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3375_, v_x_3376_, v_x_3377_, v_x_3378_);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = l_Lean_maxRecDepthErrorMessage;
v___x_3386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3388_ = l_Lean_MessageData_ofFormat(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3390_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3391_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___x_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3392_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_ref_3392_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3400_, lean_object* v_ref_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3401_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3408_, lean_object* v_ref_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3408_, v_ref_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v_fileName_3422_; lean_object* v_fileMap_3423_; lean_object* v_options_3424_; lean_object* v_currRecDepth_3425_; lean_object* v_maxRecDepth_3426_; lean_object* v_ref_3427_; lean_object* v_currNamespace_3428_; lean_object* v_openDecls_3429_; lean_object* v_initHeartbeats_3430_; lean_object* v_maxHeartbeats_3431_; lean_object* v_quotContext_3432_; lean_object* v_currMacroScope_3433_; uint8_t v_diag_3434_; lean_object* v_cancelTk_x3f_3435_; uint8_t v_suppressElabErrors_3436_; lean_object* v_inheritedTraceOptions_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3571_; 
v_fileName_3422_ = lean_ctor_get(v_a_3419_, 0);
v_fileMap_3423_ = lean_ctor_get(v_a_3419_, 1);
v_options_3424_ = lean_ctor_get(v_a_3419_, 2);
v_currRecDepth_3425_ = lean_ctor_get(v_a_3419_, 3);
v_maxRecDepth_3426_ = lean_ctor_get(v_a_3419_, 4);
v_ref_3427_ = lean_ctor_get(v_a_3419_, 5);
v_currNamespace_3428_ = lean_ctor_get(v_a_3419_, 6);
v_openDecls_3429_ = lean_ctor_get(v_a_3419_, 7);
v_initHeartbeats_3430_ = lean_ctor_get(v_a_3419_, 8);
v_maxHeartbeats_3431_ = lean_ctor_get(v_a_3419_, 9);
v_quotContext_3432_ = lean_ctor_get(v_a_3419_, 10);
v_currMacroScope_3433_ = lean_ctor_get(v_a_3419_, 11);
v_diag_3434_ = lean_ctor_get_uint8(v_a_3419_, sizeof(void*)*14);
v_cancelTk_x3f_3435_ = lean_ctor_get(v_a_3419_, 12);
v_suppressElabErrors_3436_ = lean_ctor_get_uint8(v_a_3419_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3437_ = lean_ctor_get(v_a_3419_, 13);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3439_ = v_a_3419_;
v_isShared_3440_ = v_isSharedCheck_3571_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_inheritedTraceOptions_3437_);
lean_inc(v_cancelTk_x3f_3435_);
lean_inc(v_currMacroScope_3433_);
lean_inc(v_quotContext_3432_);
lean_inc(v_maxHeartbeats_3431_);
lean_inc(v_initHeartbeats_3430_);
lean_inc(v_openDecls_3429_);
lean_inc(v_currNamespace_3428_);
lean_inc(v_ref_3427_);
lean_inc(v_maxRecDepth_3426_);
lean_inc(v_currRecDepth_3425_);
lean_inc(v_options_3424_);
lean_inc(v_fileMap_3423_);
lean_inc(v_fileName_3422_);
lean_dec(v_a_3419_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3571_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_eq(v_currRecDepth_3425_, v_maxRecDepth_3426_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; uint8_t v_transparency_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3442_ = l_Lean_Meta_Context_config(v_a_3417_);
v_transparency_3443_ = lean_ctor_get_uint8(v___x_3442_, 9);
v___x_3444_ = lean_unsigned_to_nat(1u);
v___x_3445_ = lean_nat_add(v_currRecDepth_3425_, v___x_3444_);
lean_dec(v_currRecDepth_3425_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 3, v___x_3445_);
v___x_3447_ = v___x_3439_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_fileName_3422_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_fileMap_3423_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_options_3424_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_maxRecDepth_3426_);
lean_ctor_set(v_reuseFailAlloc_3569_, 5, v_ref_3427_);
lean_ctor_set(v_reuseFailAlloc_3569_, 6, v_currNamespace_3428_);
lean_ctor_set(v_reuseFailAlloc_3569_, 7, v_openDecls_3429_);
lean_ctor_set(v_reuseFailAlloc_3569_, 8, v_initHeartbeats_3430_);
lean_ctor_set(v_reuseFailAlloc_3569_, 9, v_maxHeartbeats_3431_);
lean_ctor_set(v_reuseFailAlloc_3569_, 10, v_quotContext_3432_);
lean_ctor_set(v_reuseFailAlloc_3569_, 11, v_currMacroScope_3433_);
lean_ctor_set(v_reuseFailAlloc_3569_, 12, v_cancelTk_x3f_3435_);
lean_ctor_set(v_reuseFailAlloc_3569_, 13, v_inheritedTraceOptions_3437_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*14, v_diag_3434_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*14 + 1, v_suppressElabErrors_3436_);
v___x_3447_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___y_3449_; uint8_t v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; uint8_t v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; uint8_t v___y_3459_; uint8_t v___y_3488_; uint8_t v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = 1;
v___x_3568_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3443_, v___x_3567_);
if (v___x_3568_ == 0)
{
v___y_3488_ = v_transparency_3443_;
goto v___jp_3487_;
}
else
{
v___y_3488_ = v___x_3567_;
goto v___jp_3487_;
}
v___jp_3448_:
{
lean_object* v___x_3460_; uint8_t v_foApprox_3461_; uint8_t v_ctxApprox_3462_; uint8_t v_quasiPatternApprox_3463_; uint8_t v_constApprox_3464_; uint8_t v_isDefEqStuckEx_3465_; uint8_t v_unificationHints_3466_; uint8_t v_proofIrrelevance_3467_; uint8_t v_assignSyntheticOpaque_3468_; uint8_t v_offsetCnstrs_3469_; uint8_t v_transparency_3470_; uint8_t v_univApprox_3471_; uint8_t v_zetaUnused_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3486_; 
v___x_3460_ = l_Lean_Meta_Context_config(v___y_3452_);
lean_dec_ref(v___y_3452_);
v_foApprox_3461_ = lean_ctor_get_uint8(v___x_3460_, 0);
v_ctxApprox_3462_ = lean_ctor_get_uint8(v___x_3460_, 1);
v_quasiPatternApprox_3463_ = lean_ctor_get_uint8(v___x_3460_, 2);
v_constApprox_3464_ = lean_ctor_get_uint8(v___x_3460_, 3);
v_isDefEqStuckEx_3465_ = lean_ctor_get_uint8(v___x_3460_, 4);
v_unificationHints_3466_ = lean_ctor_get_uint8(v___x_3460_, 5);
v_proofIrrelevance_3467_ = lean_ctor_get_uint8(v___x_3460_, 6);
v_assignSyntheticOpaque_3468_ = lean_ctor_get_uint8(v___x_3460_, 7);
v_offsetCnstrs_3469_ = lean_ctor_get_uint8(v___x_3460_, 8);
v_transparency_3470_ = lean_ctor_get_uint8(v___x_3460_, 9);
v_univApprox_3471_ = lean_ctor_get_uint8(v___x_3460_, 11);
v_zetaUnused_3472_ = lean_ctor_get_uint8(v___x_3460_, 17);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3474_ = v___x_3460_;
v_isShared_3475_ = v_isSharedCheck_3486_;
goto v_resetjp_3473_;
}
else
{
lean_dec(v___x_3460_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3486_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
uint8_t v___x_3476_; uint8_t v___x_3477_; uint8_t v___x_3478_; lean_object* v___x_3480_; 
v___x_3476_ = 1;
v___x_3477_ = 0;
v___x_3478_ = 2;
if (v_isShared_3475_ == 0)
{
v___x_3480_ = v___x_3474_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 0, v_foApprox_3461_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 1, v_ctxApprox_3462_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 2, v_quasiPatternApprox_3463_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 3, v_constApprox_3464_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 4, v_isDefEqStuckEx_3465_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 5, v_unificationHints_3466_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 6, v_proofIrrelevance_3467_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 7, v_assignSyntheticOpaque_3468_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 8, v_offsetCnstrs_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 9, v_transparency_3470_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 11, v_univApprox_3471_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, 17, v_zetaUnused_3472_);
v___x_3480_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
uint64_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_ctor_set_uint8(v___x_3480_, 10, v___x_3477_);
lean_ctor_set_uint8(v___x_3480_, 12, v___x_3476_);
lean_ctor_set_uint8(v___x_3480_, 13, v___x_3476_);
lean_ctor_set_uint8(v___x_3480_, 14, v___x_3478_);
lean_ctor_set_uint8(v___x_3480_, 15, v___x_3476_);
lean_ctor_set_uint8(v___x_3480_, 16, v___x_3476_);
lean_ctor_set_uint8(v___x_3480_, 18, v___x_3476_);
v___x_3481_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3480_);
v___x_3482_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set_uint64(v___x_3482_, sizeof(void*)*1, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
lean_ctor_set(v___x_3483_, 1, v___y_3455_);
lean_ctor_set(v___x_3483_, 2, v___y_3457_);
lean_ctor_set(v___x_3483_, 3, v___y_3458_);
lean_ctor_set(v___x_3483_, 4, v___y_3449_);
lean_ctor_set(v___x_3483_, 5, v___y_3456_);
lean_ctor_set(v___x_3483_, 6, v___y_3454_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7, v___y_3450_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 1, v___y_3453_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 2, v___y_3451_);
lean_ctor_set_uint8(v___x_3483_, sizeof(void*)*7 + 3, v___y_3459_);
v___x_3484_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3416_, v___x_3483_, v_a_3418_, v___x_3447_, v_a_3420_);
lean_dec(v_a_3420_);
lean_dec_ref(v___x_3447_);
lean_dec(v_a_3418_);
return v___x_3484_;
}
}
}
v___jp_3487_:
{
uint8_t v_foApprox_3489_; uint8_t v_ctxApprox_3490_; uint8_t v_quasiPatternApprox_3491_; uint8_t v_constApprox_3492_; uint8_t v_isDefEqStuckEx_3493_; uint8_t v_unificationHints_3494_; uint8_t v_proofIrrelevance_3495_; uint8_t v_assignSyntheticOpaque_3496_; uint8_t v_offsetCnstrs_3497_; uint8_t v_etaStruct_3498_; uint8_t v_univApprox_3499_; uint8_t v_iota_3500_; uint8_t v_beta_3501_; uint8_t v_proj_3502_; uint8_t v_zeta_3503_; uint8_t v_zetaDelta_3504_; uint8_t v_zetaUnused_3505_; uint8_t v_zetaHave_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3566_; 
v_foApprox_3489_ = lean_ctor_get_uint8(v___x_3442_, 0);
v_ctxApprox_3490_ = lean_ctor_get_uint8(v___x_3442_, 1);
v_quasiPatternApprox_3491_ = lean_ctor_get_uint8(v___x_3442_, 2);
v_constApprox_3492_ = lean_ctor_get_uint8(v___x_3442_, 3);
v_isDefEqStuckEx_3493_ = lean_ctor_get_uint8(v___x_3442_, 4);
v_unificationHints_3494_ = lean_ctor_get_uint8(v___x_3442_, 5);
v_proofIrrelevance_3495_ = lean_ctor_get_uint8(v___x_3442_, 6);
v_assignSyntheticOpaque_3496_ = lean_ctor_get_uint8(v___x_3442_, 7);
v_offsetCnstrs_3497_ = lean_ctor_get_uint8(v___x_3442_, 8);
v_etaStruct_3498_ = lean_ctor_get_uint8(v___x_3442_, 10);
v_univApprox_3499_ = lean_ctor_get_uint8(v___x_3442_, 11);
v_iota_3500_ = lean_ctor_get_uint8(v___x_3442_, 12);
v_beta_3501_ = lean_ctor_get_uint8(v___x_3442_, 13);
v_proj_3502_ = lean_ctor_get_uint8(v___x_3442_, 14);
v_zeta_3503_ = lean_ctor_get_uint8(v___x_3442_, 15);
v_zetaDelta_3504_ = lean_ctor_get_uint8(v___x_3442_, 16);
v_zetaUnused_3505_ = lean_ctor_get_uint8(v___x_3442_, 17);
v_zetaHave_3506_ = lean_ctor_get_uint8(v___x_3442_, 18);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3508_ = v___x_3442_;
v_isShared_3509_ = v_isSharedCheck_3566_;
goto v_resetjp_3507_;
}
else
{
lean_dec(v___x_3442_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3566_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
uint8_t v_trackZetaDelta_3510_; lean_object* v_zetaDeltaSet_3511_; lean_object* v_lctx_3512_; lean_object* v_localInstances_3513_; lean_object* v_defEqCtx_x3f_3514_; lean_object* v_synthPendingDepth_3515_; lean_object* v_canUnfold_x3f_3516_; uint8_t v_univApprox_3517_; uint8_t v_inTypeClassResolution_3518_; uint8_t v_cacheInferType_3519_; lean_object* v_config_3521_; 
v_trackZetaDelta_3510_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*7);
v_zetaDeltaSet_3511_ = lean_ctor_get(v_a_3417_, 1);
lean_inc(v_zetaDeltaSet_3511_);
v_lctx_3512_ = lean_ctor_get(v_a_3417_, 2);
lean_inc_ref(v_lctx_3512_);
v_localInstances_3513_ = lean_ctor_get(v_a_3417_, 3);
lean_inc_ref(v_localInstances_3513_);
v_defEqCtx_x3f_3514_ = lean_ctor_get(v_a_3417_, 4);
lean_inc(v_defEqCtx_x3f_3514_);
v_synthPendingDepth_3515_ = lean_ctor_get(v_a_3417_, 5);
lean_inc(v_synthPendingDepth_3515_);
v_canUnfold_x3f_3516_ = lean_ctor_get(v_a_3417_, 6);
lean_inc(v_canUnfold_x3f_3516_);
v_univApprox_3517_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3518_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*7 + 2);
v_cacheInferType_3519_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*7 + 3);
if (v_isShared_3509_ == 0)
{
v_config_3521_ = v___x_3508_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 0, v_foApprox_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 1, v_ctxApprox_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 2, v_quasiPatternApprox_3491_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 3, v_constApprox_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 4, v_isDefEqStuckEx_3493_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 5, v_unificationHints_3494_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 6, v_proofIrrelevance_3495_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 7, v_assignSyntheticOpaque_3496_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 8, v_offsetCnstrs_3497_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 10, v_etaStruct_3498_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 11, v_univApprox_3499_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 12, v_iota_3500_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 13, v_beta_3501_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 14, v_proj_3502_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 15, v_zeta_3503_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 16, v_zetaDelta_3504_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 17, v_zetaUnused_3505_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, 18, v_zetaHave_3506_);
v_config_3521_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
uint64_t v___x_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3557_; 
lean_ctor_set_uint8(v_config_3521_, 9, v___y_3488_);
v___x_3522_ = l_Lean_Meta_Context_configKey(v_a_3417_);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; lean_object* v_unused_3559_; lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; lean_object* v_unused_3563_; lean_object* v_unused_3564_; 
v_unused_3558_ = lean_ctor_get(v_a_3417_, 6);
lean_dec(v_unused_3558_);
v_unused_3559_ = lean_ctor_get(v_a_3417_, 5);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_a_3417_, 4);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_a_3417_, 3);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_a_3417_, 2);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_a_3417_, 1);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_a_3417_, 0);
lean_dec(v_unused_3564_);
v___x_3524_ = v_a_3417_;
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v_a_3417_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3557_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
uint64_t v___x_3526_; uint64_t v___x_3527_; uint64_t v___x_3528_; uint64_t v___x_3529_; uint64_t v_key_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3526_ = 2ULL;
v___x_3527_ = lean_uint64_shift_right(v___x_3522_, v___x_3526_);
v___x_3528_ = lean_uint64_shift_left(v___x_3527_, v___x_3526_);
v___x_3529_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3488_);
v_key_3530_ = lean_uint64_lor(v___x_3528_, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3531_, 0, v_config_3521_);
lean_ctor_set_uint64(v___x_3531_, sizeof(void*)*1, v_key_3530_);
lean_inc(v_canUnfold_x3f_3516_);
lean_inc(v_synthPendingDepth_3515_);
lean_inc(v_defEqCtx_x3f_3514_);
lean_inc_ref(v_localInstances_3513_);
lean_inc_ref(v_lctx_3512_);
lean_inc(v_zetaDeltaSet_3511_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3531_);
v___x_3533_ = v___x_3524_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_zetaDeltaSet_3511_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_lctx_3512_);
lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_localInstances_3513_);
lean_ctor_set(v_reuseFailAlloc_3556_, 4, v_defEqCtx_x3f_3514_);
lean_ctor_set(v_reuseFailAlloc_3556_, 5, v_synthPendingDepth_3515_);
lean_ctor_set(v_reuseFailAlloc_3556_, 6, v_canUnfold_x3f_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*7, v_trackZetaDelta_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*7 + 1, v_univApprox_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3556_, sizeof(void*)*7 + 3, v_cacheInferType_3519_);
v___x_3533_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_Meta_getConfig___redArg(v___x_3533_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; uint8_t v_beta_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3534_);
v_beta_3536_ = lean_ctor_get_uint8(v_a_3535_, 13);
if (v_beta_3536_ == 0)
{
lean_dec(v_a_3535_);
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
uint8_t v_iota_3537_; 
v_iota_3537_ = lean_ctor_get_uint8(v_a_3535_, 12);
if (v_iota_3537_ == 0)
{
lean_dec(v_a_3535_);
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
uint8_t v_zeta_3538_; 
v_zeta_3538_ = lean_ctor_get_uint8(v_a_3535_, 15);
if (v_zeta_3538_ == 0)
{
lean_dec(v_a_3535_);
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
uint8_t v_zetaHave_3539_; 
v_zetaHave_3539_ = lean_ctor_get_uint8(v_a_3535_, 18);
if (v_zetaHave_3539_ == 0)
{
lean_dec(v_a_3535_);
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
uint8_t v_zetaDelta_3540_; 
v_zetaDelta_3540_ = lean_ctor_get_uint8(v_a_3535_, 16);
if (v_zetaDelta_3540_ == 0)
{
lean_dec(v_a_3535_);
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
uint8_t v_etaStruct_3541_; uint8_t v_proj_3542_; uint8_t v___x_3543_; uint8_t v___x_3544_; 
v_etaStruct_3541_ = lean_ctor_get_uint8(v_a_3535_, 10);
v_proj_3542_ = lean_ctor_get_uint8(v_a_3535_, 14);
lean_dec(v_a_3535_);
v___x_3543_ = 2;
v___x_3544_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
uint8_t v___x_3545_; uint8_t v___x_3546_; 
v___x_3545_ = 0;
v___x_3546_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3541_, v___x_3545_);
if (v___x_3546_ == 0)
{
v___y_3449_ = v_defEqCtx_x3f_3514_;
v___y_3450_ = v_trackZetaDelta_3510_;
v___y_3451_ = v_inTypeClassResolution_3518_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_univApprox_3517_;
v___y_3454_ = v_canUnfold_x3f_3516_;
v___y_3455_ = v_zetaDeltaSet_3511_;
v___y_3456_ = v_synthPendingDepth_3515_;
v___y_3457_ = v_lctx_3512_;
v___y_3458_ = v_localInstances_3513_;
v___y_3459_ = v_cacheInferType_3519_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3547_; 
lean_dec(v_canUnfold_x3f_3516_);
lean_dec(v_synthPendingDepth_3515_);
lean_dec(v_defEqCtx_x3f_3514_);
lean_dec_ref(v_localInstances_3513_);
lean_dec_ref(v_lctx_3512_);
lean_dec(v_zetaDeltaSet_3511_);
v___x_3547_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3416_, v___x_3533_, v_a_3418_, v___x_3447_, v_a_3420_);
lean_dec(v_a_3420_);
lean_dec_ref(v___x_3447_);
lean_dec(v_a_3418_);
return v___x_3547_;
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
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec_ref(v___x_3533_);
lean_dec(v_canUnfold_x3f_3516_);
lean_dec(v_synthPendingDepth_3515_);
lean_dec(v_defEqCtx_x3f_3514_);
lean_dec_ref(v_localInstances_3513_);
lean_dec_ref(v_lctx_3512_);
lean_dec(v_zetaDeltaSet_3511_);
lean_dec_ref(v___x_3447_);
lean_dec(v_a_3420_);
lean_dec(v_a_3418_);
lean_dec_ref(v_e_3416_);
v_a_3548_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3534_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3534_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
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
lean_object* v___x_3570_; 
lean_del_object(v___x_3439_);
lean_dec_ref(v_inheritedTraceOptions_3437_);
lean_dec(v_cancelTk_x3f_3435_);
lean_dec(v_currMacroScope_3433_);
lean_dec(v_quotContext_3432_);
lean_dec(v_maxHeartbeats_3431_);
lean_dec(v_initHeartbeats_3430_);
lean_dec(v_openDecls_3429_);
lean_dec(v_currNamespace_3428_);
lean_dec(v_maxRecDepth_3426_);
lean_dec(v_currRecDepth_3425_);
lean_dec_ref(v_options_3424_);
lean_dec_ref(v_fileMap_3423_);
lean_dec_ref(v_fileName_3422_);
lean_dec(v_a_3420_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_e_3416_);
v___x_3570_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3427_);
return v___x_3570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = lean_infer_type(v_e_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
return v_res_3578_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3579_){
_start:
{
switch(lean_obj_tag(v_x_3579_))
{
case 0:
{
uint8_t v___x_3580_; 
v___x_3580_ = 1;
return v___x_3580_;
}
case 2:
{
lean_object* v_a_3581_; lean_object* v_a_3582_; uint8_t v___x_3583_; 
v_a_3581_ = lean_ctor_get(v_x_3579_, 0);
v_a_3582_ = lean_ctor_get(v_x_3579_, 1);
v___x_3583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3581_);
if (v___x_3583_ == 0)
{
return v___x_3583_;
}
else
{
v_x_3579_ = v_a_3582_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v_x_3579_, 1);
v_x_3579_ = v_a_3585_;
goto _start;
}
default: 
{
uint8_t v___x_3587_; 
v___x_3587_ = 0;
return v___x_3587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3588_){
_start:
{
uint8_t v_res_3589_; lean_object* v_r_3590_; 
v_res_3589_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3588_);
lean_dec(v_x_3588_);
v_r_3590_ = lean_box(v_res_3589_);
return v_r_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v_mctx_3595_; lean_object* v___x_3596_; lean_object* v_fst_3597_; lean_object* v_snd_3598_; lean_object* v___x_3599_; lean_object* v_cache_3600_; lean_object* v_zetaDeltaFVarIds_3601_; lean_object* v_postponed_3602_; lean_object* v_diag_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
v___x_3594_ = lean_st_ref_get(v___y_3592_);
v_mctx_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_ref(v_mctx_3595_);
lean_dec(v___x_3594_);
v___x_3596_ = lean_instantiate_level_mvars(v_mctx_3595_, v_l_3591_);
v_fst_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_fst_3597_);
v_snd_3598_ = lean_ctor_get(v___x_3596_, 1);
lean_inc(v_snd_3598_);
lean_dec_ref(v___x_3596_);
v___x_3599_ = lean_st_ref_take(v___y_3592_);
v_cache_3600_ = lean_ctor_get(v___x_3599_, 1);
v_zetaDeltaFVarIds_3601_ = lean_ctor_get(v___x_3599_, 2);
v_postponed_3602_ = lean_ctor_get(v___x_3599_, 3);
v_diag_3603_ = lean_ctor_get(v___x_3599_, 4);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v___x_3599_, 0);
lean_dec(v_unused_3613_);
v___x_3605_ = v___x_3599_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_diag_3603_);
lean_inc(v_postponed_3602_);
lean_inc(v_zetaDeltaFVarIds_3601_);
lean_inc(v_cache_3600_);
lean_dec(v___x_3599_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v_fst_3597_);
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_fst_3597_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_cache_3600_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_zetaDeltaFVarIds_3601_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_postponed_3602_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_diag_3603_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_st_ref_set(v___y_3592_, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_snd_3598_);
return v___x_3610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3614_, v___y_3615_);
lean_dec(v___y_3615_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3618_, v___y_3620_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
switch(lean_obj_tag(v_x_3632_))
{
case 3:
{
lean_object* v_u_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_u_3643_ = lean_ctor_get(v_x_3632_, 0);
lean_inc(v_u_3643_);
lean_dec_ref(v_x_3632_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v___x_3645_ = lean_nat_dec_eq(v_x_3633_, v___x_3644_);
lean_dec(v_x_3633_);
if (v___x_3645_ == 0)
{
lean_dec(v_u_3643_);
goto v___jp_3639_;
}
else
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3643_, v_a_3635_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3657_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3657_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3657_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
uint8_t v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3651_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3647_);
lean_dec(v_a_3647_);
v___x_3652_ = l_Bool_toLBool(v___x_3651_);
v___x_3653_ = lean_box(v___x_3652_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v___x_3653_);
v___x_3655_ = v___x_3649_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
v_a_3658_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3646_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3646_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3666_; lean_object* v_zero_3667_; uint8_t v_isZero_3668_; 
v_body_3666_ = lean_ctor_get(v_x_3632_, 2);
lean_inc_ref(v_body_3666_);
lean_dec_ref(v_x_3632_);
v_zero_3667_ = lean_unsigned_to_nat(0u);
v_isZero_3668_ = lean_nat_dec_eq(v_x_3633_, v_zero_3667_);
if (v_isZero_3668_ == 1)
{
uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec_ref(v_body_3666_);
lean_dec(v_x_3633_);
v___x_3669_ = 0;
v___x_3670_ = lean_box(v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
return v___x_3671_;
}
else
{
lean_object* v_one_3672_; lean_object* v_n_3673_; 
v_one_3672_ = lean_unsigned_to_nat(1u);
v_n_3673_ = lean_nat_sub(v_x_3633_, v_one_3672_);
lean_dec(v_x_3633_);
v_x_3632_ = v_body_3666_;
v_x_3633_ = v_n_3673_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3675_; 
v_body_3675_ = lean_ctor_get(v_x_3632_, 3);
lean_inc_ref(v_body_3675_);
lean_dec_ref(v_x_3632_);
v_x_3632_ = v_body_3675_;
goto _start;
}
case 10:
{
lean_object* v_expr_3677_; 
v_expr_3677_ = lean_ctor_get(v_x_3632_, 1);
lean_inc_ref(v_expr_3677_);
lean_dec_ref(v_x_3632_);
v_x_3632_ = v_expr_3677_;
goto _start;
}
default: 
{
lean_dec(v_x_3633_);
lean_dec_ref(v_x_3632_);
goto v___jp_3639_;
}
}
v___jp_3639_:
{
uint8_t v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = 2;
v___x_3641_ = lean_box(v___x_3640_);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3679_, v_x_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
switch(lean_obj_tag(v_x_3687_))
{
case 4:
{
lean_object* v_declName_3694_; lean_object* v_us_3695_; lean_object* v___x_3696_; 
v_declName_3694_ = lean_ctor_get(v_x_3687_, 0);
lean_inc(v_declName_3694_);
v_us_3695_ = lean_ctor_get(v_x_3687_, 1);
lean_inc(v_us_3695_);
lean_dec_ref(v_x_3687_);
v___x_3696_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3694_, v_us_3695_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref(v___x_3696_);
v___x_3698_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3697_, v_x_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_x_3688_);
v_a_3699_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3696_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3696_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3707_; lean_object* v___x_3708_; 
v_fvarId_3707_ = lean_ctor_get(v_x_3687_, 0);
lean_inc(v_fvarId_3707_);
lean_dec_ref(v_x_3687_);
lean_inc_ref(v_a_3689_);
v___x_3708_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3707_, v_a_3689_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref(v___x_3708_);
v___x_3710_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3709_, v_x_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3710_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_x_3688_);
v_a_3711_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3708_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3708_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3719_; lean_object* v___x_3720_; 
v_mvarId_3719_ = lean_ctor_get(v_x_3687_, 0);
lean_inc(v_mvarId_3719_);
lean_dec_ref(v_x_3687_);
v___x_3720_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3719_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref(v___x_3720_);
v___x_3722_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3721_, v_x_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
return v___x_3722_;
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec(v_x_3688_);
v_a_3723_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3720_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3720_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
case 5:
{
lean_object* v_fn_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_fn_3731_ = lean_ctor_get(v_x_3687_, 0);
lean_inc_ref(v_fn_3731_);
lean_dec_ref(v_x_3687_);
v___x_3732_ = lean_unsigned_to_nat(1u);
v___x_3733_ = lean_nat_add(v_x_3688_, v___x_3732_);
lean_dec(v_x_3688_);
v_x_3687_ = v_fn_3731_;
v_x_3688_ = v___x_3733_;
goto _start;
}
case 10:
{
lean_object* v_expr_3735_; 
v_expr_3735_ = lean_ctor_get(v_x_3687_, 1);
lean_inc_ref(v_expr_3735_);
lean_dec_ref(v_x_3687_);
v_x_3687_ = v_expr_3735_;
goto _start;
}
case 8:
{
lean_object* v_body_3737_; 
v_body_3737_ = lean_ctor_get(v_x_3687_, 3);
lean_inc_ref(v_body_3737_);
lean_dec_ref(v_x_3687_);
v_x_3687_ = v_body_3737_;
goto _start;
}
case 6:
{
lean_object* v_body_3739_; lean_object* v_zero_3740_; uint8_t v_isZero_3741_; 
v_body_3739_ = lean_ctor_get(v_x_3687_, 2);
lean_inc_ref(v_body_3739_);
lean_dec_ref(v_x_3687_);
v_zero_3740_ = lean_unsigned_to_nat(0u);
v_isZero_3741_ = lean_nat_dec_eq(v_x_3688_, v_zero_3740_);
if (v_isZero_3741_ == 1)
{
uint8_t v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v_body_3739_);
lean_dec(v_x_3688_);
v___x_3742_ = 0;
v___x_3743_ = lean_box(v___x_3742_);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
else
{
lean_object* v_one_3745_; lean_object* v_n_3746_; 
v_one_3745_ = lean_unsigned_to_nat(1u);
v_n_3746_ = lean_nat_sub(v_x_3688_, v_one_3745_);
lean_dec(v_x_3688_);
v_x_3687_ = v_body_3739_;
v_x_3688_ = v_n_3746_;
goto _start;
}
}
default: 
{
uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec(v_x_3688_);
lean_dec_ref(v_x_3687_);
v___x_3748_ = 2;
v___x_3749_ = lean_box(v___x_3748_);
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
return v___x_3750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3751_, lean_object* v_x_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3751_, v_x_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_a_3754_);
lean_dec_ref(v_a_3753_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
switch(lean_obj_tag(v_x_3759_))
{
case 0:
{
uint8_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_dec_ref(v_x_3759_);
v___x_3765_ = 2;
v___x_3766_ = lean_box(v___x_3765_);
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
return v___x_3767_;
}
case 1:
{
lean_object* v_fvarId_3768_; lean_object* v___x_3769_; 
v_fvarId_3768_ = lean_ctor_get(v_x_3759_, 0);
lean_inc(v_fvarId_3768_);
lean_dec_ref(v_x_3759_);
lean_inc_ref(v_a_3760_);
v___x_3769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3768_, v_a_3760_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(0u);
v___x_3772_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3770_, v___x_3771_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
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
case 2:
{
lean_object* v_mvarId_3781_; lean_object* v___x_3782_; 
v_mvarId_3781_ = lean_ctor_get(v_x_3759_, 0);
lean_inc(v_mvarId_3781_);
lean_dec_ref(v_x_3759_);
v___x_3782_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3781_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = lean_unsigned_to_nat(0u);
v___x_3785_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3783_, v___x_3784_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
return v___x_3785_;
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_a_3786_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3782_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3782_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
case 4:
{
lean_object* v_declName_3794_; lean_object* v_us_3795_; lean_object* v___x_3796_; 
v_declName_3794_ = lean_ctor_get(v_x_3759_, 0);
lean_inc(v_declName_3794_);
v_us_3795_ = lean_ctor_get(v_x_3759_, 1);
lean_inc(v_us_3795_);
lean_dec_ref(v_x_3759_);
v___x_3796_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3794_, v_us_3795_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref(v___x_3796_);
v___x_3798_ = lean_unsigned_to_nat(0u);
v___x_3799_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3797_, v___x_3798_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
return v___x_3799_;
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
v_a_3800_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3796_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
case 5:
{
lean_object* v_fn_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v_fn_3808_ = lean_ctor_get(v_x_3759_, 0);
lean_inc_ref(v_fn_3808_);
lean_dec_ref(v_x_3759_);
v___x_3809_ = lean_unsigned_to_nat(1u);
v___x_3810_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_3808_, v___x_3809_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
return v___x_3810_;
}
case 7:
{
lean_object* v_body_3811_; 
v_body_3811_ = lean_ctor_get(v_x_3759_, 2);
lean_inc_ref(v_body_3811_);
lean_dec_ref(v_x_3759_);
v_x_3759_ = v_body_3811_;
goto _start;
}
case 8:
{
lean_object* v_body_3813_; 
v_body_3813_ = lean_ctor_get(v_x_3759_, 3);
lean_inc_ref(v_body_3813_);
lean_dec_ref(v_x_3759_);
v_x_3759_ = v_body_3813_;
goto _start;
}
case 10:
{
lean_object* v_expr_3815_; 
v_expr_3815_ = lean_ctor_get(v_x_3759_, 1);
lean_inc_ref(v_expr_3815_);
lean_dec_ref(v_x_3759_);
v_x_3759_ = v_expr_3815_;
goto _start;
}
case 11:
{
uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_dec_ref(v_x_3759_);
v___x_3817_ = 2;
v___x_3818_ = lean_box(v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
return v___x_3819_;
}
default: 
{
uint8_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_dec_ref(v_x_3759_);
v___x_3820_ = 0;
v___x_3821_ = lean_box(v___x_3820_);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
return v___x_3822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Meta_isPropQuick(v_x_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v___x_3836_; 
lean_inc_ref(v_e_3830_);
v___x_3836_ = l_Lean_Meta_isPropQuick(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3893_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3893_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3893_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
uint8_t v___x_3841_; 
v___x_3841_ = lean_unbox(v_a_3837_);
lean_dec(v_a_3837_);
switch(v___x_3841_)
{
case 0:
{
uint8_t v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec_ref(v_e_3830_);
v___x_3842_ = 0;
v___x_3843_ = lean_box(v___x_3842_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3843_);
v___x_3845_ = v___x_3839_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
case 1:
{
uint8_t v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
lean_dec_ref(v_e_3830_);
v___x_3847_ = 1;
v___x_3848_ = lean_box(v___x_3847_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3848_);
v___x_3850_ = v___x_3839_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
default: 
{
lean_object* v___x_3852_; 
lean_del_object(v___x_3839_);
lean_inc(v_a_3834_);
lean_inc_ref(v_a_3833_);
lean_inc(v_a_3832_);
lean_inc_ref(v_a_3831_);
v___x_3852_ = lean_infer_type(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l_Lean_Meta_whnfD(v_a_3853_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3876_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3876_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3876_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
if (lean_obj_tag(v_a_3855_) == 3)
{
lean_object* v_u_3859_; lean_object* v___x_3860_; lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3870_; 
lean_del_object(v___x_3857_);
v_u_3859_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_u_3859_);
lean_dec_ref(v_a_3855_);
v___x_3860_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3859_, v_a_3832_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
uint8_t v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3865_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3861_);
lean_dec(v_a_3861_);
v___x_3866_ = lean_box(v___x_3865_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3866_);
v___x_3868_ = v___x_3863_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
else
{
uint8_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_dec(v_a_3855_);
v___x_3871_ = 0;
v___x_3872_ = lean_box(v___x_3871_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3872_);
v___x_3874_ = v___x_3857_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_a_3877_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3854_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3854_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3852_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3852_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec_ref(v_e_3830_);
v_a_3894_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3836_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3836_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Meta_isProp(v_e_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_3909_){
_start:
{
switch(lean_obj_tag(v_x_3909_))
{
case 0:
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_unsigned_to_nat(0u);
return v___x_3910_;
}
case 1:
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_unsigned_to_nat(1u);
return v___x_3911_;
}
case 2:
{
lean_object* v___x_3912_; 
v___x_3912_ = lean_unsigned_to_nat(2u);
return v___x_3912_;
}
default: 
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_unsigned_to_nat(3u);
return v___x_3913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_3914_);
lean_dec(v_x_3914_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_3916_, lean_object* v_k_3917_){
_start:
{
if (lean_obj_tag(v_t_3916_) == 3)
{
lean_object* v_idx_3918_; lean_object* v___x_3919_; 
v_idx_3918_ = lean_ctor_get(v_t_3916_, 0);
lean_inc(v_idx_3918_);
lean_dec_ref(v_t_3916_);
v___x_3919_ = lean_apply_1(v_k_3917_, v_idx_3918_);
return v___x_3919_;
}
else
{
lean_dec(v_t_3916_);
return v_k_3917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_3920_, lean_object* v_ctorIdx_3921_, lean_object* v_t_3922_, lean_object* v_h_3923_, lean_object* v_k_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3922_, v_k_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_3926_, lean_object* v_ctorIdx_3927_, lean_object* v_t_3928_, lean_object* v_h_3929_, lean_object* v_k_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_3926_, v_ctorIdx_3927_, v_t_3928_, v_h_3929_, v_k_3930_);
lean_dec(v_ctorIdx_3927_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_3932_, lean_object* v_false_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3932_, v_false_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_3935_, lean_object* v_t_3936_, lean_object* v_h_3937_, lean_object* v_false_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3936_, v_false_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_3940_, lean_object* v_true_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3940_, v_true_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_3943_, lean_object* v_t_3944_, lean_object* v_h_3945_, lean_object* v_true_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3944_, v_true_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_3948_, lean_object* v_undef_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3948_, v_undef_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_3951_, lean_object* v_t_3952_, lean_object* v_h_3953_, lean_object* v_undef_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3952_, v_undef_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_3956_, lean_object* v_bvar_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3956_, v_bvar_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_3959_, lean_object* v_t_3960_, lean_object* v_h_3961_, lean_object* v_bvar_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3960_, v_bvar_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_3964_){
_start:
{
switch(v_x_3964_)
{
case 0:
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_box(0);
return v___x_3965_;
}
case 1:
{
lean_object* v___x_3966_; 
v___x_3966_ = lean_box(1);
return v___x_3966_;
}
default: 
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_box(2);
return v___x_3967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_3968_){
_start:
{
uint8_t v_x_25__boxed_3969_; lean_object* v_res_3970_; 
v_x_25__boxed_3969_ = lean_unbox(v_x_3968_);
v_res_3970_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_3969_);
return v_res_3970_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_3971_){
_start:
{
switch(lean_obj_tag(v_x_3971_))
{
case 0:
{
uint8_t v___x_3972_; 
v___x_3972_ = 0;
return v___x_3972_;
}
case 1:
{
uint8_t v___x_3973_; 
v___x_3973_ = 1;
return v___x_3973_;
}
default: 
{
uint8_t v___x_3974_; 
v___x_3974_ = 2;
return v___x_3974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_3975_){
_start:
{
uint8_t v_res_3976_; lean_object* v_r_3977_; 
v_res_3976_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_3975_);
lean_dec(v_x_3975_);
v_r_3977_ = lean_box(v_res_3976_);
return v_r_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_3979_){
_start:
{
switch(lean_obj_tag(v_e_3979_))
{
case 3:
{
lean_object* v_u_3980_; uint8_t v___x_3981_; 
v_u_3980_ = lean_ctor_get(v_e_3979_, 0);
v___x_3981_ = l_Lean_Level_isNeverZero(v_u_3980_);
if (v___x_3981_ == 0)
{
uint8_t v___x_3982_; 
v___x_3982_ = l_Lean_Level_isZero(v_u_3980_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_box(2);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_box(1);
return v___x_3984_;
}
}
else
{
lean_object* v___x_3985_; 
v___x_3985_ = lean_box(0);
return v___x_3985_;
}
}
case 5:
{
lean_object* v_fn_3986_; 
v_fn_3986_ = lean_ctor_get(v_e_3979_, 0);
if (lean_obj_tag(v_fn_3986_) == 4)
{
lean_object* v_declName_3987_; 
v_declName_3987_ = lean_ctor_get(v_fn_3986_, 0);
if (lean_obj_tag(v_declName_3987_) == 1)
{
lean_object* v_pre_3988_; 
v_pre_3988_ = lean_ctor_get(v_declName_3987_, 0);
if (lean_obj_tag(v_pre_3988_) == 0)
{
lean_object* v_arg_3989_; lean_object* v_str_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v_arg_3989_ = lean_ctor_get(v_e_3979_, 1);
v_str_3990_ = lean_ctor_get(v_declName_3987_, 1);
v___x_3991_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_3992_ = lean_string_dec_eq(v_str_3990_, v___x_3991_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_box(2);
return v___x_3993_;
}
else
{
v_e_3979_ = v_arg_3989_;
goto _start;
}
}
else
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_box(2);
return v___x_3995_;
}
}
else
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_box(2);
return v___x_3996_;
}
}
else
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_box(2);
return v___x_3997_;
}
}
default: 
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_box(2);
return v___x_3998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_3999_);
lean_dec_ref(v_e_3999_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4001_, lean_object* v_binderType_4002_){
_start:
{
if (lean_obj_tag(v_r_4001_) == 3)
{
lean_object* v_idx_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4015_; 
v_idx_4003_ = lean_ctor_get(v_r_4001_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v_r_4001_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4005_ = v_r_4001_;
v_isShared_4006_ = v_isSharedCheck_4015_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_idx_4003_);
lean_dec(v_r_4001_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4015_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v_zero_4007_; uint8_t v_isZero_4008_; 
v_zero_4007_ = lean_unsigned_to_nat(0u);
v_isZero_4008_ = lean_nat_dec_eq(v_idx_4003_, v_zero_4007_);
if (v_isZero_4008_ == 1)
{
lean_object* v___x_4009_; 
lean_del_object(v___x_4005_);
lean_dec(v_idx_4003_);
v___x_4009_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4002_);
return v___x_4009_;
}
else
{
lean_object* v_one_4010_; lean_object* v_n_4011_; lean_object* v___x_4013_; 
v_one_4010_ = lean_unsigned_to_nat(1u);
v_n_4011_ = lean_nat_sub(v_idx_4003_, v_one_4010_);
lean_dec(v_idx_4003_);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v_n_4011_);
v___x_4013_ = v___x_4005_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_n_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
return v_r_4001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4016_, lean_object* v_binderType_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4016_, v_binderType_4017_);
lean_dec_ref(v_binderType_4017_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4019_, lean_object* v_x_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_type_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; 
switch(lean_obj_tag(v_x_4019_))
{
case 7:
{
lean_object* v_binderType_4054_; lean_object* v_body_4055_; lean_object* v_zero_4056_; uint8_t v_isZero_4057_; 
v_binderType_4054_ = lean_ctor_get(v_x_4019_, 1);
v_body_4055_ = lean_ctor_get(v_x_4019_, 2);
v_zero_4056_ = lean_unsigned_to_nat(0u);
v_isZero_4057_ = lean_nat_dec_eq(v_x_4020_, v_zero_4056_);
if (v_isZero_4057_ == 1)
{
v_type_4027_ = v_x_4019_;
v___y_4028_ = v_a_4021_;
v___y_4029_ = v_a_4022_;
v___y_4030_ = v_a_4023_;
v___y_4031_ = v_a_4024_;
goto v___jp_4026_;
}
else
{
lean_object* v_one_4058_; lean_object* v_n_4059_; lean_object* v___x_4060_; 
lean_inc_ref(v_body_4055_);
lean_inc_ref(v_binderType_4054_);
lean_dec_ref(v_x_4019_);
v_one_4058_ = lean_unsigned_to_nat(1u);
v_n_4059_ = lean_nat_sub(v_x_4020_, v_one_4058_);
v___x_4060_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4055_, v_n_4059_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
lean_dec(v_n_4059_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4069_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4069_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4069_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4067_; 
v___x_4065_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4061_, v_binderType_4054_);
lean_dec_ref(v_binderType_4054_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4065_);
v___x_4067_ = v___x_4063_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
else
{
lean_dec_ref(v_binderType_4054_);
return v___x_4060_;
}
}
}
case 8:
{
lean_object* v_type_4070_; lean_object* v_body_4071_; lean_object* v___x_4072_; 
v_type_4070_ = lean_ctor_get(v_x_4019_, 1);
lean_inc_ref(v_type_4070_);
v_body_4071_ = lean_ctor_get(v_x_4019_, 3);
lean_inc_ref(v_body_4071_);
lean_dec_ref(v_x_4019_);
v___x_4072_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4071_, v_x_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4081_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4081_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4081_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4077_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4073_, v_type_4070_);
lean_dec_ref(v_type_4070_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___x_4077_);
v___x_4079_ = v___x_4075_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
else
{
lean_dec_ref(v_type_4070_);
return v___x_4072_;
}
}
case 10:
{
lean_object* v_expr_4082_; 
v_expr_4082_ = lean_ctor_get(v_x_4019_, 1);
lean_inc_ref(v_expr_4082_);
lean_dec_ref(v_x_4019_);
v_x_4019_ = v_expr_4082_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v_deBruijnIndex_4084_ = lean_ctor_get(v_x_4019_, 0);
lean_inc(v_deBruijnIndex_4084_);
lean_dec_ref(v_x_4019_);
v___x_4085_ = lean_unsigned_to_nat(0u);
v___x_4086_ = lean_nat_dec_eq(v_x_4020_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_dec(v_deBruijnIndex_4084_);
goto v___jp_4051_;
}
else
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_deBruijnIndex_4084_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
}
default: 
{
lean_object* v___x_4089_; uint8_t v___x_4090_; 
v___x_4089_ = lean_unsigned_to_nat(0u);
v___x_4090_ = lean_nat_dec_eq(v_x_4020_, v___x_4089_);
if (v___x_4090_ == 0)
{
lean_dec_ref(v_x_4019_);
goto v___jp_4051_;
}
else
{
v_type_4027_ = v_x_4019_;
v___y_4028_ = v_a_4021_;
v___y_4029_ = v_a_4022_;
v___y_4030_ = v_a_4023_;
v___y_4031_ = v_a_4024_;
goto v___jp_4026_;
}
}
}
v___jp_4026_:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_Meta_isPropQuick(v_type_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4042_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4042_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4042_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
uint8_t v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4037_ = lean_unbox(v_a_4033_);
lean_dec(v_a_4033_);
v___x_4038_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4037_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4038_);
v___x_4040_ = v___x_4035_;
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
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4032_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4032_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
v___jp_4051_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_box(2);
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
return v___x_4053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4091_, lean_object* v_x_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4091_, v_x_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_x_4092_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4099_, lean_object* v_n_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4099_, v_n_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4116_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4111_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4107_);
lean_dec(v_a_4107_);
v___x_4112_ = lean_box(v___x_4111_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v___x_4112_);
v___x_4114_ = v___x_4109_;
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
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
v_a_4117_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4106_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4106_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4125_, lean_object* v_n_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4125_, v_n_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_n_4126_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4133_, lean_object* v_x_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
switch(lean_obj_tag(v_x_4133_))
{
case 4:
{
lean_object* v_declName_4140_; lean_object* v_us_4141_; lean_object* v___x_4142_; 
v_declName_4140_ = lean_ctor_get(v_x_4133_, 0);
lean_inc(v_declName_4140_);
v_us_4141_ = lean_ctor_get(v_x_4133_, 1);
lean_inc(v_us_4141_);
lean_dec_ref(v_x_4133_);
v___x_4142_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4140_, v_us_4141_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4143_, v_x_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_x_4134_);
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v_x_4134_);
v_a_4145_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4142_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4142_);
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
case 1:
{
lean_object* v_fvarId_4153_; lean_object* v___x_4154_; 
v_fvarId_4153_ = lean_ctor_get(v_x_4133_, 0);
lean_inc(v_fvarId_4153_);
lean_dec_ref(v_x_4133_);
lean_inc_ref(v_a_4135_);
v___x_4154_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4153_, v_a_4135_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v___x_4154_);
v___x_4156_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4155_, v_x_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_x_4134_);
return v___x_4156_;
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_x_4134_);
v_a_4157_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4154_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4154_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4165_; lean_object* v___x_4166_; 
v_mvarId_4165_ = lean_ctor_get(v_x_4133_, 0);
lean_inc(v_mvarId_4165_);
lean_dec_ref(v_x_4133_);
v___x_4166_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4165_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref(v___x_4166_);
v___x_4168_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4167_, v_x_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_x_4134_);
return v___x_4168_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v_x_4134_);
v_a_4169_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4166_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4166_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
case 5:
{
lean_object* v_fn_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_fn_4177_ = lean_ctor_get(v_x_4133_, 0);
lean_inc_ref(v_fn_4177_);
lean_dec_ref(v_x_4133_);
v___x_4178_ = lean_unsigned_to_nat(1u);
v___x_4179_ = lean_nat_add(v_x_4134_, v___x_4178_);
lean_dec(v_x_4134_);
v_x_4133_ = v_fn_4177_;
v_x_4134_ = v___x_4179_;
goto _start;
}
case 10:
{
lean_object* v_expr_4181_; 
v_expr_4181_ = lean_ctor_get(v_x_4133_, 1);
lean_inc_ref(v_expr_4181_);
lean_dec_ref(v_x_4133_);
v_x_4133_ = v_expr_4181_;
goto _start;
}
case 8:
{
lean_object* v_body_4183_; 
v_body_4183_ = lean_ctor_get(v_x_4133_, 3);
lean_inc_ref(v_body_4183_);
lean_dec_ref(v_x_4133_);
v_x_4133_ = v_body_4183_;
goto _start;
}
case 6:
{
lean_object* v_body_4185_; lean_object* v_zero_4186_; uint8_t v_isZero_4187_; 
v_body_4185_ = lean_ctor_get(v_x_4133_, 2);
lean_inc_ref(v_body_4185_);
lean_dec_ref(v_x_4133_);
v_zero_4186_ = lean_unsigned_to_nat(0u);
v_isZero_4187_ = lean_nat_dec_eq(v_x_4134_, v_zero_4186_);
if (v_isZero_4187_ == 1)
{
lean_object* v___x_4188_; 
lean_dec(v_x_4134_);
v___x_4188_ = l_Lean_Meta_isProofQuick(v_body_4185_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4188_;
}
else
{
lean_object* v_one_4189_; lean_object* v_n_4190_; 
v_one_4189_ = lean_unsigned_to_nat(1u);
v_n_4190_ = lean_nat_sub(v_x_4134_, v_one_4189_);
lean_dec(v_x_4134_);
v_x_4133_ = v_body_4185_;
v_x_4134_ = v_n_4190_;
goto _start;
}
}
default: 
{
uint8_t v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec(v_x_4134_);
lean_dec_ref(v_x_4133_);
v___x_4192_ = 2;
v___x_4193_ = lean_box(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_){
_start:
{
switch(lean_obj_tag(v_x_4195_))
{
case 0:
{
uint8_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
lean_dec_ref(v_x_4195_);
v___x_4201_ = 2;
v___x_4202_ = lean_box(v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
return v___x_4203_;
}
case 1:
{
lean_object* v_fvarId_4204_; lean_object* v___x_4205_; 
v_fvarId_4204_ = lean_ctor_get(v_x_4195_, 0);
lean_inc(v_fvarId_4204_);
lean_dec_ref(v_x_4195_);
lean_inc_ref(v_a_4196_);
v___x_4205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4204_, v_a_4196_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
v___x_4207_ = lean_unsigned_to_nat(0u);
v___x_4208_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4206_, v___x_4207_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
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
case 2:
{
lean_object* v_mvarId_4217_; lean_object* v___x_4218_; 
v_mvarId_4217_ = lean_ctor_get(v_x_4195_, 0);
lean_inc(v_mvarId_4217_);
lean_dec_ref(v_x_4195_);
v___x_4218_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4217_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4219_);
lean_dec_ref(v___x_4218_);
v___x_4220_ = lean_unsigned_to_nat(0u);
v___x_4221_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4219_, v___x_4220_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
return v___x_4221_;
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
v_a_4222_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4218_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4218_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
case 4:
{
lean_object* v_declName_4230_; lean_object* v_us_4231_; lean_object* v___x_4232_; 
v_declName_4230_ = lean_ctor_get(v_x_4195_, 0);
lean_inc(v_declName_4230_);
v_us_4231_ = lean_ctor_get(v_x_4195_, 1);
lean_inc(v_us_4231_);
lean_dec_ref(v_x_4195_);
v___x_4232_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4230_, v_us_4231_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
v___x_4234_ = lean_unsigned_to_nat(0u);
v___x_4235_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4233_, v___x_4234_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
return v___x_4235_;
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4232_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4232_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
case 5:
{
lean_object* v_fn_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_fn_4244_ = lean_ctor_get(v_x_4195_, 0);
lean_inc_ref(v_fn_4244_);
lean_dec_ref(v_x_4195_);
v___x_4245_ = lean_unsigned_to_nat(1u);
v___x_4246_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4244_, v___x_4245_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
return v___x_4246_;
}
case 6:
{
lean_object* v_body_4247_; 
v_body_4247_ = lean_ctor_get(v_x_4195_, 2);
lean_inc_ref(v_body_4247_);
lean_dec_ref(v_x_4195_);
v_x_4195_ = v_body_4247_;
goto _start;
}
case 8:
{
lean_object* v_body_4249_; 
v_body_4249_ = lean_ctor_get(v_x_4195_, 3);
lean_inc_ref(v_body_4249_);
lean_dec_ref(v_x_4195_);
v_x_4195_ = v_body_4249_;
goto _start;
}
case 10:
{
lean_object* v_expr_4251_; 
v_expr_4251_ = lean_ctor_get(v_x_4195_, 1);
lean_inc_ref(v_expr_4251_);
lean_dec_ref(v_x_4195_);
v_x_4195_ = v_expr_4251_;
goto _start;
}
case 11:
{
uint8_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
lean_dec_ref(v_x_4195_);
v___x_4253_ = 2;
v___x_4254_ = lean_box(v___x_4253_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
default: 
{
uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec_ref(v_x_4195_);
v___x_4256_ = 0;
v___x_4257_ = lean_box(v___x_4256_);
v___x_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
return v___x_4258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_Meta_isProofQuick(v_x_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4266_, lean_object* v_x_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4266_, v_x_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v___x_4280_; 
lean_inc_ref(v_e_4274_);
v___x_4280_ = l_Lean_Meta_isProofQuick(v_e_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4307_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4307_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4307_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
uint8_t v___x_4285_; 
v___x_4285_ = lean_unbox(v_a_4281_);
lean_dec(v_a_4281_);
switch(v___x_4285_)
{
case 0:
{
uint8_t v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4289_; 
lean_dec_ref(v_e_4274_);
v___x_4286_ = 0;
v___x_4287_ = lean_box(v___x_4286_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4287_);
v___x_4289_ = v___x_4283_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
case 1:
{
uint8_t v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4294_; 
lean_dec_ref(v_e_4274_);
v___x_4291_ = 1;
v___x_4292_ = lean_box(v___x_4291_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4292_);
v___x_4294_ = v___x_4283_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4292_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
default: 
{
lean_object* v___x_4296_; 
lean_del_object(v___x_4283_);
lean_inc(v_a_4278_);
lean_inc_ref(v_a_4277_);
lean_inc(v_a_4276_);
lean_inc_ref(v_a_4275_);
v___x_4296_ = lean_infer_type(v_e_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___x_4296_);
v___x_4298_ = l_Lean_Meta_isProp(v_a_4297_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
return v___x_4298_;
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_a_4299_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4296_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4296_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v_e_4274_);
v_a_4308_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4280_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4280_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Meta_isProof(v_e_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4323_, lean_object* v_x_4324_){
_start:
{
switch(lean_obj_tag(v_x_4323_))
{
case 3:
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = lean_unsigned_to_nat(0u);
v___x_4331_ = lean_nat_dec_eq(v_x_4324_, v___x_4330_);
lean_dec(v_x_4324_);
if (v___x_4331_ == 0)
{
goto v___jp_4326_;
}
else
{
uint8_t v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = 1;
v___x_4333_ = lean_box(v___x_4332_);
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
return v___x_4334_;
}
}
case 7:
{
lean_object* v_body_4335_; lean_object* v_zero_4336_; uint8_t v_isZero_4337_; 
v_body_4335_ = lean_ctor_get(v_x_4323_, 2);
v_zero_4336_ = lean_unsigned_to_nat(0u);
v_isZero_4337_ = lean_nat_dec_eq(v_x_4324_, v_zero_4336_);
if (v_isZero_4337_ == 1)
{
uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_dec(v_x_4324_);
v___x_4338_ = 0;
v___x_4339_ = lean_box(v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
return v___x_4340_;
}
else
{
lean_object* v_one_4341_; lean_object* v_n_4342_; 
v_one_4341_ = lean_unsigned_to_nat(1u);
v_n_4342_ = lean_nat_sub(v_x_4324_, v_one_4341_);
lean_dec(v_x_4324_);
v_x_4323_ = v_body_4335_;
v_x_4324_ = v_n_4342_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4344_; 
v_body_4344_ = lean_ctor_get(v_x_4323_, 3);
v_x_4323_ = v_body_4344_;
goto _start;
}
case 10:
{
lean_object* v_expr_4346_; 
v_expr_4346_ = lean_ctor_get(v_x_4323_, 1);
v_x_4323_ = v_expr_4346_;
goto _start;
}
default: 
{
lean_dec(v_x_4324_);
goto v___jp_4326_;
}
}
v___jp_4326_:
{
uint8_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = 2;
v___x_4328_ = lean_box(v___x_4327_);
v___x_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
return v___x_4329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4348_, lean_object* v_x_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4348_, v_x_4349_);
lean_dec_ref(v_x_4348_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4352_, lean_object* v_x_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4352_, v_x_4353_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4360_, lean_object* v_x_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4360_, v_x_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
lean_dec(v_a_4365_);
lean_dec_ref(v_a_4364_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec_ref(v_x_4360_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4368_, lean_object* v_x_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
switch(lean_obj_tag(v_x_4368_))
{
case 4:
{
lean_object* v_declName_4375_; lean_object* v_us_4376_; lean_object* v___x_4377_; 
v_declName_4375_ = lean_ctor_get(v_x_4368_, 0);
lean_inc(v_declName_4375_);
v_us_4376_ = lean_ctor_get(v_x_4368_, 1);
lean_inc(v_us_4376_);
lean_dec_ref(v_x_4368_);
v___x_4377_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4375_, v_us_4376_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4378_, v_x_4369_);
lean_dec(v_a_4378_);
return v___x_4379_;
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_x_4369_);
v_a_4380_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4377_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4377_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4388_; lean_object* v___x_4389_; 
v_fvarId_4388_ = lean_ctor_get(v_x_4368_, 0);
lean_inc(v_fvarId_4388_);
lean_dec_ref(v_x_4368_);
lean_inc_ref(v_a_4370_);
v___x_4389_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4388_, v_a_4370_, v_a_4372_, v_a_4373_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4391_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc(v_a_4390_);
lean_dec_ref(v___x_4389_);
v___x_4391_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4390_, v_x_4369_);
lean_dec(v_a_4390_);
return v___x_4391_;
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_dec(v_x_4369_);
v_a_4392_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4389_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4389_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4400_; lean_object* v___x_4401_; 
v_mvarId_4400_ = lean_ctor_get(v_x_4368_, 0);
lean_inc(v_mvarId_4400_);
lean_dec_ref(v_x_4368_);
v___x_4401_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4400_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref(v___x_4401_);
v___x_4403_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4402_, v_x_4369_);
lean_dec(v_a_4402_);
return v___x_4403_;
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_x_4369_);
v_a_4404_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4401_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4401_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
case 5:
{
lean_object* v_fn_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_fn_4412_ = lean_ctor_get(v_x_4368_, 0);
lean_inc_ref(v_fn_4412_);
lean_dec_ref(v_x_4368_);
v___x_4413_ = lean_unsigned_to_nat(1u);
v___x_4414_ = lean_nat_add(v_x_4369_, v___x_4413_);
lean_dec(v_x_4369_);
v_x_4368_ = v_fn_4412_;
v_x_4369_ = v___x_4414_;
goto _start;
}
case 10:
{
lean_object* v_expr_4416_; 
v_expr_4416_ = lean_ctor_get(v_x_4368_, 1);
lean_inc_ref(v_expr_4416_);
lean_dec_ref(v_x_4368_);
v_x_4368_ = v_expr_4416_;
goto _start;
}
case 8:
{
lean_object* v_body_4418_; 
v_body_4418_ = lean_ctor_get(v_x_4368_, 3);
lean_inc_ref(v_body_4418_);
lean_dec_ref(v_x_4368_);
v_x_4368_ = v_body_4418_;
goto _start;
}
case 6:
{
lean_object* v_body_4420_; lean_object* v_zero_4421_; uint8_t v_isZero_4422_; 
v_body_4420_ = lean_ctor_get(v_x_4368_, 2);
lean_inc_ref(v_body_4420_);
lean_dec_ref(v_x_4368_);
v_zero_4421_ = lean_unsigned_to_nat(0u);
v_isZero_4422_ = lean_nat_dec_eq(v_x_4369_, v_zero_4421_);
if (v_isZero_4422_ == 1)
{
uint8_t v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_dec_ref(v_body_4420_);
lean_dec(v_x_4369_);
v___x_4423_ = 0;
v___x_4424_ = lean_box(v___x_4423_);
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
return v___x_4425_;
}
else
{
lean_object* v_one_4426_; lean_object* v_n_4427_; 
v_one_4426_ = lean_unsigned_to_nat(1u);
v_n_4427_ = lean_nat_sub(v_x_4369_, v_one_4426_);
lean_dec(v_x_4369_);
v_x_4368_ = v_body_4420_;
v_x_4369_ = v_n_4427_;
goto _start;
}
}
default: 
{
uint8_t v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
lean_dec(v_x_4369_);
lean_dec_ref(v_x_4368_);
v___x_4429_ = 2;
v___x_4430_ = lean_box(v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
return v___x_4431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4432_, lean_object* v_x_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4432_, v_x_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
switch(lean_obj_tag(v_x_4440_))
{
case 1:
{
lean_object* v_fvarId_4446_; lean_object* v___x_4447_; 
v_fvarId_4446_ = lean_ctor_get(v_x_4440_, 0);
lean_inc(v_fvarId_4446_);
lean_dec_ref(v_x_4440_);
lean_inc_ref(v_a_4441_);
v___x_4447_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4446_, v_a_4441_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref(v___x_4447_);
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4448_, v___x_4449_);
lean_dec(v_a_4448_);
return v___x_4450_;
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4447_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4447_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4459_; lean_object* v___x_4460_; 
v_mvarId_4459_ = lean_ctor_get(v_x_4440_, 0);
lean_inc(v_mvarId_4459_);
lean_dec_ref(v_x_4440_);
v___x_4460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4459_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref(v___x_4460_);
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4461_, v___x_4462_);
lean_dec(v_a_4461_);
return v___x_4463_;
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
v_a_4464_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4460_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4460_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
case 3:
{
uint8_t v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_dec_ref(v_x_4440_);
v___x_4472_ = 1;
v___x_4473_ = lean_box(v___x_4472_);
v___x_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
return v___x_4474_;
}
case 4:
{
lean_object* v_declName_4475_; lean_object* v_us_4476_; lean_object* v___x_4477_; 
v_declName_4475_ = lean_ctor_get(v_x_4440_, 0);
lean_inc(v_declName_4475_);
v_us_4476_ = lean_ctor_get(v_x_4440_, 1);
lean_inc(v_us_4476_);
lean_dec_ref(v_x_4440_);
v___x_4477_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4475_, v_us_4476_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref(v___x_4477_);
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4478_, v___x_4479_);
lean_dec(v_a_4478_);
return v___x_4480_;
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_a_4481_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4477_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4477_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
case 5:
{
lean_object* v_fn_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_fn_4489_ = lean_ctor_get(v_x_4440_, 0);
lean_inc_ref(v_fn_4489_);
lean_dec_ref(v_x_4440_);
v___x_4490_ = lean_unsigned_to_nat(1u);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4489_, v___x_4490_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4491_;
}
case 6:
{
uint8_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
lean_dec_ref(v_x_4440_);
v___x_4492_ = 0;
v___x_4493_ = lean_box(v___x_4492_);
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
return v___x_4494_;
}
case 7:
{
uint8_t v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
lean_dec_ref(v_x_4440_);
v___x_4495_ = 1;
v___x_4496_ = lean_box(v___x_4495_);
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
case 8:
{
lean_object* v_body_4498_; 
v_body_4498_ = lean_ctor_get(v_x_4440_, 3);
lean_inc_ref(v_body_4498_);
lean_dec_ref(v_x_4440_);
v_x_4440_ = v_body_4498_;
goto _start;
}
case 9:
{
uint8_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
lean_dec_ref(v_x_4440_);
v___x_4500_ = 0;
v___x_4501_ = lean_box(v___x_4500_);
v___x_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
return v___x_4502_;
}
case 10:
{
lean_object* v_expr_4503_; 
v_expr_4503_ = lean_ctor_get(v_x_4440_, 1);
lean_inc_ref(v_expr_4503_);
lean_dec_ref(v_x_4440_);
v_x_4440_ = v_expr_4503_;
goto _start;
}
default: 
{
uint8_t v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
lean_dec_ref(v_x_4440_);
v___x_4505_ = 2;
v___x_4506_ = lean_box(v___x_4505_);
v___x_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
return v___x_4507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_Meta_isTypeQuick(v_x_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v___x_4521_; 
lean_inc_ref(v_e_4515_);
v___x_4521_ = l_Lean_Meta_isTypeQuick(v_e_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4571_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4524_ = v___x_4521_;
v_isShared_4525_ = v_isSharedCheck_4571_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4521_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4571_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
uint8_t v___x_4526_; 
v___x_4526_ = lean_unbox(v_a_4522_);
lean_dec(v_a_4522_);
switch(v___x_4526_)
{
case 0:
{
uint8_t v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
lean_dec_ref(v_e_4515_);
v___x_4527_ = 0;
v___x_4528_ = lean_box(v___x_4527_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v___x_4528_);
v___x_4530_ = v___x_4524_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
case 1:
{
uint8_t v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
lean_dec_ref(v_e_4515_);
v___x_4532_ = 1;
v___x_4533_ = lean_box(v___x_4532_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v___x_4533_);
v___x_4535_ = v___x_4524_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
default: 
{
lean_object* v___x_4537_; 
lean_del_object(v___x_4524_);
lean_inc(v_a_4519_);
lean_inc_ref(v_a_4518_);
lean_inc(v_a_4517_);
lean_inc_ref(v_a_4516_);
v___x_4537_ = lean_infer_type(v_e_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4539_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref(v___x_4537_);
v___x_4539_ = l_Lean_Meta_whnfD(v_a_4538_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4554_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4542_ = v___x_4539_;
v_isShared_4543_ = v_isSharedCheck_4554_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4554_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
if (lean_obj_tag(v_a_4540_) == 3)
{
uint8_t v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; 
lean_dec_ref(v_a_4540_);
v___x_4544_ = 1;
v___x_4545_ = lean_box(v___x_4544_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4545_);
v___x_4547_ = v___x_4542_;
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
else
{
uint8_t v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4552_; 
lean_dec(v_a_4540_);
v___x_4549_ = 0;
v___x_4550_ = lean_box(v___x_4549_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4550_);
v___x_4552_ = v___x_4542_;
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
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
v_a_4555_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4539_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4539_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
v_a_4563_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4537_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4537_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v_e_4515_);
v_a_4572_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4521_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4521_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Meta_isType(v_e_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4587_){
_start:
{
switch(lean_obj_tag(v_x_4587_))
{
case 7:
{
lean_object* v_body_4588_; 
v_body_4588_ = lean_ctor_get(v_x_4587_, 2);
v_x_4587_ = v_body_4588_;
goto _start;
}
case 3:
{
lean_object* v_u_4590_; lean_object* v___x_4591_; 
v_u_4590_ = lean_ctor_get(v_x_4587_, 0);
lean_inc(v_u_4590_);
v___x_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4591_, 0, v_u_4590_);
return v___x_4591_;
}
default: 
{
lean_object* v___x_4592_; 
v___x_4592_ = lean_box(0);
return v___x_4592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4593_);
lean_dec_ref(v_x_4593_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4595_, lean_object* v_body_4596_, lean_object* v_x_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4595_, v_body_4596_, v_x_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4606_, lean_object* v_xs_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
switch(lean_obj_tag(v_type_4606_))
{
case 3:
{
lean_object* v_u_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
lean_dec_ref(v_xs_4607_);
v_u_4613_ = lean_ctor_get(v_type_4606_, 0);
lean_inc(v_u_4613_);
lean_dec_ref(v_type_4606_);
v___x_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4614_, 0, v_u_4613_);
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
case 7:
{
lean_object* v_binderName_4616_; lean_object* v_binderType_4617_; lean_object* v_body_4618_; uint8_t v_binderInfo_4619_; lean_object* v___f_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_binderName_4616_ = lean_ctor_get(v_type_4606_, 0);
lean_inc(v_binderName_4616_);
v_binderType_4617_ = lean_ctor_get(v_type_4606_, 1);
lean_inc_ref(v_binderType_4617_);
v_body_4618_ = lean_ctor_get(v_type_4606_, 2);
lean_inc_ref(v_body_4618_);
v_binderInfo_4619_ = lean_ctor_get_uint8(v_type_4606_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_4606_);
lean_inc_ref(v_xs_4607_);
v___f_4620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4620_, 0, v_xs_4607_);
lean_closure_set(v___f_4620_, 1, v_body_4618_);
v___x_4621_ = lean_expr_instantiate_rev(v_binderType_4617_, v_xs_4607_);
lean_dec_ref(v_xs_4607_);
lean_dec_ref(v_binderType_4617_);
lean_inc_ref(v_a_4608_);
v___x_4622_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4616_, v_binderInfo_4619_, v___x_4621_, v___f_4620_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
return v___x_4622_;
}
default: 
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = lean_expr_instantiate_rev(v_type_4606_, v_xs_4607_);
lean_dec_ref(v_xs_4607_);
lean_dec_ref(v_type_4606_);
v___x_4624_ = l_Lean_Meta_whnfD(v___x_4623_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4640_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4640_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4640_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
switch(lean_obj_tag(v_a_4625_))
{
case 3:
{
lean_object* v_u_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v_u_4629_ = lean_ctor_get(v_a_4625_, 0);
lean_inc(v_u_4629_);
lean_dec_ref(v_a_4625_);
v___x_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4630_, 0, v_u_4629_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v___x_4630_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
case 7:
{
lean_object* v___x_4634_; 
lean_del_object(v___x_4627_);
v___x_4634_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4606_ = v_a_4625_;
v_xs_4607_ = v___x_4634_;
goto _start;
}
default: 
{
lean_object* v___x_4636_; lean_object* v___x_4638_; 
lean_dec(v_a_4625_);
v___x_4636_ = lean_box(0);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v___x_4636_);
v___x_4638_ = v___x_4627_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
v_a_4641_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4624_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4624_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4649_, lean_object* v_body_4650_, lean_object* v_x_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_array_push(v_xs_4649_, v_x_4651_);
v___x_4658_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4650_, v___x_4657_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4659_, lean_object* v_xs_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4659_, v_xs_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4667_, lean_object* v_cache_4668_, lean_object* v_a_x3f_4669_){
_start:
{
lean_object* v___x_4671_; lean_object* v_mctx_4672_; lean_object* v_zetaDeltaFVarIds_4673_; lean_object* v_postponed_4674_; lean_object* v_diag_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4685_; 
v___x_4671_ = lean_st_ref_take(v_a_4667_);
v_mctx_4672_ = lean_ctor_get(v___x_4671_, 0);
v_zetaDeltaFVarIds_4673_ = lean_ctor_get(v___x_4671_, 2);
v_postponed_4674_ = lean_ctor_get(v___x_4671_, 3);
v_diag_4675_ = lean_ctor_get(v___x_4671_, 4);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4685_ == 0)
{
lean_object* v_unused_4686_; 
v_unused_4686_ = lean_ctor_get(v___x_4671_, 1);
lean_dec(v_unused_4686_);
v___x_4677_ = v___x_4671_;
v_isShared_4678_ = v_isSharedCheck_4685_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_diag_4675_);
lean_inc(v_postponed_4674_);
lean_inc(v_zetaDeltaFVarIds_4673_);
lean_inc(v_mctx_4672_);
lean_dec(v___x_4671_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4685_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 1, v_cache_4668_);
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_mctx_4672_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v_cache_4668_);
lean_ctor_set(v_reuseFailAlloc_4684_, 2, v_zetaDeltaFVarIds_4673_);
lean_ctor_set(v_reuseFailAlloc_4684_, 3, v_postponed_4674_);
lean_ctor_set(v_reuseFailAlloc_4684_, 4, v_diag_4675_);
v___x_4680_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = lean_st_ref_set(v_a_4667_, v___x_4680_);
v___x_4682_ = lean_box(0);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
return v___x_4683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4687_, lean_object* v_cache_4688_, lean_object* v_a_x3f_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4687_, v_cache_4688_, v_a_x3f_4689_);
lean_dec(v_a_x3f_4689_);
lean_dec(v_a_4687_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4692_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v___x_4699_; lean_object* v_cache_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4699_ = lean_st_ref_get(v_a_4694_);
v_cache_4700_ = lean_ctor_get(v___x_4699_, 1);
lean_inc_ref(v_cache_4700_);
lean_dec(v___x_4699_);
v___x_4701_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4702_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4692_, v___x_4701_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4719_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4705_ = v___x_4702_;
v_isShared_4706_ = v_isSharedCheck_4719_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4719_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
lean_inc(v_a_4703_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set_tag(v___x_4705_, 1);
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
v___x_4709_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4694_, v_cache_4700_, v___x_4708_);
lean_dec_ref(v___x_4708_);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4716_ == 0)
{
lean_object* v_unused_4717_; 
v_unused_4717_ = lean_ctor_get(v___x_4709_, 0);
lean_dec(v_unused_4717_);
v___x_4711_ = v___x_4709_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_dec(v___x_4709_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 0, v_a_4703_);
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4703_);
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
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
v_a_4720_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4720_);
lean_dec_ref(v___x_4702_);
v___x_4721_ = lean_box(0);
v___x_4722_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4694_, v_cache_4700_, v___x_4721_);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4729_ == 0)
{
lean_object* v_unused_4730_; 
v_unused_4730_ = lean_ctor_get(v___x_4722_, 0);
lean_dec(v_unused_4730_);
v___x_4724_ = v___x_4722_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_dec(v___x_4722_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 1);
lean_ctor_set(v___x_4724_, 0, v_a_4720_);
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4720_);
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
else
{
lean_object* v___x_4731_; 
lean_dec_ref(v_type_4692_);
v___x_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4698_);
return v___x_4731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
lean_dec(v_a_4736_);
lean_dec_ref(v_a_4735_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4760_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4760_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4760_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
if (lean_obj_tag(v_a_4746_) == 0)
{
uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
v___x_4750_ = 0;
v___x_4751_ = lean_box(v___x_4750_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4751_);
v___x_4753_ = v___x_4748_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
else
{
uint8_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
lean_dec_ref(v_a_4746_);
v___x_4755_ = 1;
v___x_4756_ = lean_box(v___x_4755_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v___x_4756_);
v___x_4758_ = v___x_4748_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
v_a_4761_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4745_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4745_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Meta_isTypeFormerType(v_type_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
return v_res_4775_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_4776_, lean_object* v_x_4777_){
_start:
{
if (lean_obj_tag(v_x_4776_) == 0)
{
if (lean_obj_tag(v_x_4777_) == 0)
{
uint8_t v___x_4778_; 
v___x_4778_ = 1;
return v___x_4778_;
}
else
{
uint8_t v___x_4779_; 
v___x_4779_ = 0;
return v___x_4779_;
}
}
else
{
if (lean_obj_tag(v_x_4777_) == 0)
{
uint8_t v___x_4780_; 
v___x_4780_ = 0;
return v___x_4780_;
}
else
{
lean_object* v_val_4781_; lean_object* v_val_4782_; uint8_t v___x_4783_; 
v_val_4781_ = lean_ctor_get(v_x_4776_, 0);
v_val_4782_ = lean_ctor_get(v_x_4777_, 0);
v___x_4783_ = lean_level_eq(v_val_4781_, v_val_4782_);
return v___x_4783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_4784_, lean_object* v_x_4785_){
_start:
{
uint8_t v_res_4786_; lean_object* v_r_4787_; 
v_res_4786_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_4784_, v_x_4785_);
lean_dec(v_x_4785_);
lean_dec(v_x_4784_);
v_r_4787_ = lean_box(v_res_4786_);
return v_r_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4807_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4799_ = v___x_4796_;
v_isShared_4800_ = v_isSharedCheck_4807_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4796_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4807_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
v___x_4801_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_4802_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_4797_, v___x_4801_);
lean_dec(v_a_4797_);
v___x_4803_ = lean_box(v___x_4802_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v___x_4803_);
v___x_4805_ = v___x_4799_;
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
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
v_a_4808_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4796_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4796_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Meta_isPropFormerType(v_type_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
lean_dec(v_a_4820_);
lean_dec_ref(v_a_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_a_4817_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v___x_4829_; 
lean_inc(v_a_4827_);
lean_inc_ref(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
v___x_4829_ = lean_infer_type(v_e_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref(v___x_4829_);
v___x_4831_ = l_Lean_Meta_isTypeFormerType(v_a_4830_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
return v___x_4831_;
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
v_a_4832_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4829_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4829_);
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
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Lean_Meta_isTypeFormer(v_e_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_4847_, lean_object* v_maxFVars_x3f_4848_, lean_object* v_k_4849_, uint8_t v_cleanupAnnotations_4850_, uint8_t v_whnfType_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___f_4857_; lean_object* v___x_4858_; 
v___f_4857_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4857_, 0, v_k_4849_);
v___x_4858_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4847_, v_maxFVars_x3f_4848_, v___f_4857_, v_cleanupAnnotations_4850_, v_whnfType_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4858_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4858_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
v_a_4867_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4858_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4858_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_4875_, lean_object* v_maxFVars_x3f_4876_, lean_object* v_k_4877_, lean_object* v_cleanupAnnotations_4878_, lean_object* v_whnfType_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4885_; uint8_t v_whnfType_boxed_4886_; lean_object* v_res_4887_; 
v_cleanupAnnotations_boxed_4885_ = lean_unbox(v_cleanupAnnotations_4878_);
v_whnfType_boxed_4886_ = lean_unbox(v_whnfType_4879_);
v_res_4887_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4875_, v_maxFVars_x3f_4876_, v_k_4877_, v_cleanupAnnotations_boxed_4885_, v_whnfType_boxed_4886_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_4888_, lean_object* v_type_4889_, lean_object* v_maxFVars_x3f_4890_, lean_object* v_k_4891_, uint8_t v_cleanupAnnotations_4892_, uint8_t v_whnfType_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4889_, v_maxFVars_x3f_4890_, v_k_4891_, v_cleanupAnnotations_4892_, v_whnfType_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_4900_, lean_object* v_type_4901_, lean_object* v_maxFVars_x3f_4902_, lean_object* v_k_4903_, lean_object* v_cleanupAnnotations_4904_, lean_object* v_whnfType_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4911_; uint8_t v_whnfType_boxed_4912_; lean_object* v_res_4913_; 
v_cleanupAnnotations_boxed_4911_ = lean_unbox(v_cleanupAnnotations_4904_);
v_whnfType_boxed_4912_ = lean_unbox(v_whnfType_4905_);
v_res_4913_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_4900_, v_type_4901_, v_maxFVars_x3f_4902_, v_k_4903_, v_cleanupAnnotations_boxed_4911_, v_whnfType_boxed_4912_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
return v_res_4913_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_4914_, lean_object* v_as_4915_, size_t v_i_4916_, size_t v_stop_4917_){
_start:
{
uint8_t v___x_4918_; 
v___x_4918_ = lean_usize_dec_eq(v_i_4916_, v_stop_4917_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4919_ = lean_array_uget_borrowed(v_as_4915_, v_i_4916_);
v___x_4920_ = lean_expr_eqv(v_a_4914_, v___x_4919_);
if (v___x_4920_ == 0)
{
size_t v___x_4921_; size_t v___x_4922_; 
v___x_4921_ = ((size_t)1ULL);
v___x_4922_ = lean_usize_add(v_i_4916_, v___x_4921_);
v_i_4916_ = v___x_4922_;
goto _start;
}
else
{
return v___x_4920_;
}
}
else
{
uint8_t v___x_4924_; 
v___x_4924_ = 0;
return v___x_4924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_4925_, lean_object* v_as_4926_, lean_object* v_i_4927_, lean_object* v_stop_4928_){
_start:
{
size_t v_i_boxed_4929_; size_t v_stop_boxed_4930_; uint8_t v_res_4931_; lean_object* v_r_4932_; 
v_i_boxed_4929_ = lean_unbox_usize(v_i_4927_);
lean_dec(v_i_4927_);
v_stop_boxed_4930_ = lean_unbox_usize(v_stop_4928_);
lean_dec(v_stop_4928_);
v_res_4931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4925_, v_as_4926_, v_i_boxed_4929_, v_stop_boxed_4930_);
lean_dec_ref(v_as_4926_);
lean_dec_ref(v_a_4925_);
v_r_4932_ = lean_box(v_res_4931_);
return v_r_4932_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4935_; lean_object* v___x_4936_; uint8_t v___x_4937_; 
v___x_4935_ = lean_unsigned_to_nat(0u);
v___x_4936_ = lean_array_get_size(v_as_4933_);
v___x_4937_ = lean_nat_dec_lt(v___x_4935_, v___x_4936_);
if (v___x_4937_ == 0)
{
return v___x_4937_;
}
else
{
if (v___x_4937_ == 0)
{
return v___x_4937_;
}
else
{
size_t v___x_4938_; size_t v___x_4939_; uint8_t v___x_4940_; 
v___x_4938_ = ((size_t)0ULL);
v___x_4939_ = lean_usize_of_nat(v___x_4936_);
v___x_4940_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4934_, v_as_4933_, v___x_4938_, v___x_4939_);
return v___x_4940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_4941_, lean_object* v_a_4942_){
_start:
{
uint8_t v_res_4943_; lean_object* v_r_4944_; 
v_res_4943_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_4941_, v_a_4942_);
lean_dec_ref(v_a_4942_);
lean_dec_ref(v_as_4941_);
v_r_4944_ = lean_box(v_res_4943_);
return v_r_4944_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_4945_, lean_object* v_e_4946_){
_start:
{
uint8_t v___x_4947_; lean_object* v_d_4949_; lean_object* v_b_4950_; 
v___x_4947_ = l_Lean_Expr_hasFVar(v_e_4946_);
if (v___x_4947_ == 0)
{
lean_dec_ref(v_e_4946_);
return v___x_4947_;
}
else
{
switch(lean_obj_tag(v_e_4946_))
{
case 7:
{
lean_object* v_binderType_4953_; lean_object* v_body_4954_; 
v_binderType_4953_ = lean_ctor_get(v_e_4946_, 1);
lean_inc_ref(v_binderType_4953_);
v_body_4954_ = lean_ctor_get(v_e_4946_, 2);
lean_inc_ref(v_body_4954_);
lean_dec_ref(v_e_4946_);
v_d_4949_ = v_binderType_4953_;
v_b_4950_ = v_body_4954_;
goto v___jp_4948_;
}
case 6:
{
lean_object* v_binderType_4955_; lean_object* v_body_4956_; 
v_binderType_4955_ = lean_ctor_get(v_e_4946_, 1);
lean_inc_ref(v_binderType_4955_);
v_body_4956_ = lean_ctor_get(v_e_4946_, 2);
lean_inc_ref(v_body_4956_);
lean_dec_ref(v_e_4946_);
v_d_4949_ = v_binderType_4955_;
v_b_4950_ = v_body_4956_;
goto v___jp_4948_;
}
case 10:
{
lean_object* v_expr_4957_; 
v_expr_4957_ = lean_ctor_get(v_e_4946_, 1);
lean_inc_ref(v_expr_4957_);
lean_dec_ref(v_e_4946_);
v_e_4946_ = v_expr_4957_;
goto _start;
}
case 8:
{
lean_object* v_type_4959_; lean_object* v_value_4960_; lean_object* v_body_4961_; uint8_t v___x_4962_; 
v_type_4959_ = lean_ctor_get(v_e_4946_, 1);
lean_inc_ref(v_type_4959_);
v_value_4960_ = lean_ctor_get(v_e_4946_, 2);
lean_inc_ref(v_value_4960_);
v_body_4961_ = lean_ctor_get(v_e_4946_, 3);
lean_inc_ref(v_body_4961_);
lean_dec_ref(v_e_4946_);
v___x_4962_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4945_, v_type_4959_);
if (v___x_4962_ == 0)
{
uint8_t v___x_4963_; 
v___x_4963_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4945_, v_value_4960_);
if (v___x_4963_ == 0)
{
v_e_4946_ = v_body_4961_;
goto _start;
}
else
{
lean_dec_ref(v_body_4961_);
return v___x_4947_;
}
}
else
{
lean_dec_ref(v_body_4961_);
lean_dec_ref(v_value_4960_);
return v___x_4947_;
}
}
case 5:
{
lean_object* v_fn_4965_; lean_object* v_arg_4966_; uint8_t v___x_4967_; 
v_fn_4965_ = lean_ctor_get(v_e_4946_, 0);
lean_inc_ref(v_fn_4965_);
v_arg_4966_ = lean_ctor_get(v_e_4946_, 1);
lean_inc_ref(v_arg_4966_);
lean_dec_ref(v_e_4946_);
v___x_4967_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4945_, v_fn_4965_);
if (v___x_4967_ == 0)
{
v_e_4946_ = v_arg_4966_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4966_);
return v___x_4947_;
}
}
case 11:
{
lean_object* v_struct_4969_; 
v_struct_4969_ = lean_ctor_get(v_e_4946_, 2);
lean_inc_ref(v_struct_4969_);
lean_dec_ref(v_e_4946_);
v_e_4946_ = v_struct_4969_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; 
v_fvarId_4971_ = lean_ctor_get(v_e_4946_, 0);
lean_inc(v_fvarId_4971_);
lean_dec_ref(v_e_4946_);
v___x_4972_ = l_Lean_Expr_fvar___override(v_fvarId_4971_);
v___x_4973_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_4945_, v___x_4972_);
lean_dec_ref(v___x_4972_);
return v___x_4973_;
}
default: 
{
uint8_t v___x_4974_; 
lean_dec_ref(v_e_4946_);
v___x_4974_ = 0;
return v___x_4974_;
}
}
}
v___jp_4948_:
{
uint8_t v___x_4951_; 
v___x_4951_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4945_, v_d_4949_);
if (v___x_4951_ == 0)
{
v_e_4946_ = v_b_4950_;
goto _start;
}
else
{
lean_dec_ref(v_b_4950_);
return v___x_4947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_4975_, lean_object* v_e_4976_){
_start:
{
uint8_t v_res_4977_; lean_object* v_r_4978_; 
v_res_4977_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4975_, v_e_4976_);
lean_dec_ref(v_xs_4975_);
v_r_4978_ = lean_box(v_res_4977_);
return v_r_4978_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_4981_ = l_Lean_stringToMessageData(v___x_4980_);
return v___x_4981_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_4984_ = l_Lean_stringToMessageData(v___x_4983_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_4985_, lean_object* v_type_4986_, lean_object* v_as_4987_, size_t v_sz_4988_, size_t v_i_4989_, lean_object* v_b_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v_a_4997_; uint8_t v___x_5001_; 
v___x_5001_ = lean_usize_dec_lt(v_i_4989_, v_sz_4988_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; 
lean_dec_ref(v_type_4986_);
v___x_5002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5002_, 0, v_b_4990_);
return v___x_5002_;
}
else
{
lean_object* v___x_5003_; lean_object* v_a_5004_; uint8_t v___x_5005_; 
v___x_5003_ = lean_box(0);
v_a_5004_ = lean_array_uget_borrowed(v_as_4987_, v_i_4989_);
lean_inc(v_a_5004_);
v___x_5005_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4985_, v_a_5004_);
if (v___x_5005_ == 0)
{
v_a_4997_ = v___x_5003_;
goto v___jp_4996_;
}
else
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5006_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5004_);
v___x_5007_ = l_Lean_MessageData_ofExpr(v_a_5004_);
v___x_5008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5006_);
lean_ctor_set(v___x_5008_, 1, v___x_5007_);
v___x_5009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5008_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
lean_inc_ref(v_type_4986_);
v___x_5011_ = l_Lean_MessageData_ofExpr(v_type_4986_);
v___x_5012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5010_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5012_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_dec_ref(v___x_5013_);
v_a_4997_ = v___x_5003_;
goto v___jp_4996_;
}
else
{
lean_dec_ref(v_type_4986_);
return v___x_5013_;
}
}
}
v___jp_4996_:
{
size_t v___x_4998_; size_t v___x_4999_; 
v___x_4998_ = ((size_t)1ULL);
v___x_4999_ = lean_usize_add(v_i_4989_, v___x_4998_);
v_i_4989_ = v___x_4999_;
v_b_4990_ = v_a_4997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5014_, lean_object* v_type_5015_, lean_object* v_as_5016_, lean_object* v_sz_5017_, lean_object* v_i_5018_, lean_object* v_b_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
size_t v_sz_boxed_5025_; size_t v_i_boxed_5026_; lean_object* v_res_5027_; 
v_sz_boxed_5025_ = lean_unbox_usize(v_sz_5017_);
lean_dec(v_sz_5017_);
v_i_boxed_5026_ = lean_unbox_usize(v_i_5018_);
lean_dec(v_i_5018_);
v_res_5027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5014_, v_type_5015_, v_as_5016_, v_sz_boxed_5025_, v_i_boxed_5026_, v_b_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec_ref(v_as_5016_);
lean_dec_ref(v_xs_5014_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5028_, size_t v_i_5029_, lean_object* v_bs_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
uint8_t v___x_5036_; 
v___x_5036_ = lean_usize_dec_lt(v_i_5029_, v_sz_5028_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; 
v___x_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5037_, 0, v_bs_5030_);
return v___x_5037_;
}
else
{
lean_object* v_v_5038_; lean_object* v___x_5039_; 
v_v_5038_ = lean_array_uget_borrowed(v_bs_5030_, v_i_5029_);
lean_inc(v___y_5034_);
lean_inc_ref(v___y_5033_);
lean_inc(v___y_5032_);
lean_inc_ref(v___y_5031_);
lean_inc(v_v_5038_);
v___x_5039_ = lean_infer_type(v_v_5038_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5041_; lean_object* v_bs_x27_5042_; size_t v___x_5043_; size_t v___x_5044_; lean_object* v___x_5045_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_a_5040_);
lean_dec_ref(v___x_5039_);
v___x_5041_ = lean_unsigned_to_nat(0u);
v_bs_x27_5042_ = lean_array_uset(v_bs_5030_, v_i_5029_, v___x_5041_);
v___x_5043_ = ((size_t)1ULL);
v___x_5044_ = lean_usize_add(v_i_5029_, v___x_5043_);
v___x_5045_ = lean_array_uset(v_bs_x27_5042_, v_i_5029_, v_a_5040_);
v_i_5029_ = v___x_5044_;
v_bs_5030_ = v___x_5045_;
goto _start;
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec_ref(v_bs_5030_);
v_a_5047_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5039_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5039_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5055_, lean_object* v_i_5056_, lean_object* v_bs_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
size_t v_sz_boxed_5063_; size_t v_i_boxed_5064_; lean_object* v_res_5065_; 
v_sz_boxed_5063_ = lean_unbox_usize(v_sz_5055_);
lean_dec(v_sz_5055_);
v_i_boxed_5064_ = lean_unbox_usize(v_i_5056_);
lean_dec(v_i_5056_);
v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5063_, v_i_boxed_5064_, v_bs_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
return v_res_5065_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
return v___x_5068_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5071_ = l_Lean_stringToMessageData(v___x_5070_);
return v___x_5071_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5074_ = l_Lean_stringToMessageData(v___x_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5075_, lean_object* v_n_5076_, lean_object* v_xs_5077_, lean_object* v_x_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___x_5108_; uint8_t v___x_5109_; 
v___x_5108_ = lean_array_get_size(v_xs_5077_);
v___x_5109_ = lean_nat_dec_eq(v___x_5108_, v_n_5076_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec_ref(v_xs_5077_);
v___x_5110_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5111_ = l_Lean_MessageData_ofExpr(v_type_5075_);
v___x_5112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5110_);
lean_ctor_set(v___x_5112_, 1, v___x_5111_);
v___x_5113_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5112_);
lean_ctor_set(v___x_5114_, 1, v___x_5113_);
v___x_5115_ = l_Nat_reprFast(v_n_5076_);
v___x_5116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5115_);
v___x_5117_ = l_Lean_MessageData_ofFormat(v___x_5116_);
v___x_5118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5114_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5120_, 0, v___x_5118_);
lean_ctor_set(v___x_5120_, 1, v___x_5119_);
v___x_5121_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5120_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5121_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5121_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
else
{
lean_dec(v_n_5076_);
goto v___jp_5084_;
}
v___jp_5084_:
{
size_t v_sz_5085_; size_t v___x_5086_; lean_object* v___x_5087_; 
v_sz_5085_ = lean_array_size(v_xs_5077_);
v___x_5086_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5077_);
v___x_5087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5085_, v___x_5086_, v_xs_5077_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5089_; size_t v_sz_5090_; lean_object* v___x_5091_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref(v___x_5087_);
v___x_5089_ = lean_box(0);
v_sz_5090_ = lean_array_size(v_a_5088_);
v___x_5091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5077_, v_type_5075_, v_a_5088_, v_sz_5090_, v___x_5086_, v___x_5089_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
lean_dec_ref(v_xs_5077_);
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5098_ == 0)
{
lean_object* v_unused_5099_; 
v_unused_5099_ = lean_ctor_get(v___x_5091_, 0);
lean_dec(v_unused_5099_);
v___x_5093_ = v___x_5091_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_dec(v___x_5091_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v_a_5088_);
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5088_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_dec(v_a_5088_);
v_a_5100_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5091_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5091_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5077_);
lean_dec_ref(v_type_5075_);
return v___x_5087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5130_, lean_object* v_n_5131_, lean_object* v_xs_5132_, lean_object* v_x_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5130_, v_n_5131_, v_xs_5132_, v_x_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec_ref(v_x_5133_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5140_, lean_object* v_type_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_){
_start:
{
lean_object* v___f_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; lean_object* v___x_5150_; 
lean_inc(v_n_5140_);
lean_inc_ref(v_type_5141_);
v___f_5147_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5147_, 0, v_type_5141_);
lean_closure_set(v___f_5147_, 1, v_n_5140_);
v___x_5148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5148_, 0, v_n_5140_);
v___x_5149_ = 0;
v___x_5150_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5141_, v___x_5148_, v___f_5147_, v___x_5149_, v___x_5149_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5151_, lean_object* v_type_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Lean_Meta_arrowDomainsN(v_n_5151_, v_type_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5159_, lean_object* v_e_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v___x_5166_; 
lean_inc(v_a_5164_);
lean_inc_ref(v_a_5163_);
lean_inc(v_a_5162_);
lean_inc_ref(v_a_5161_);
v___x_5166_ = lean_infer_type(v_e_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref(v___x_5166_);
v___x_5168_ = l_Lean_Meta_arrowDomainsN(v_n_5159_, v_a_5167_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
return v___x_5168_;
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_dec(v_n_5159_);
v_a_5169_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5166_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5166_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5177_, lean_object* v_e_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l_Lean_Meta_inferArgumentTypesN(v_n_5177_, v_e_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
lean_dec(v_a_5182_);
lean_dec_ref(v_a_5181_);
lean_dec(v_a_5180_);
lean_dec_ref(v_a_5179_);
return v_res_5184_;
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
