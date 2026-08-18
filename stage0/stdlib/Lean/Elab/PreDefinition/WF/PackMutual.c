// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.PackMutual
// Imports: public import Lean.Meta.ArgsPacker public import Lean.Elab.PreDefinition.WF.Eqns
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object*);
uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_withAppN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Failed to eta-expand partial application"};
static const lean_object* l_Lean_Elab_WF_withAppN___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_withAppN___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_withAppN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_withAppN___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_withAppN___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_withAppN___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_WF_packCalls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Elab.PreDefinition.WF.PackMutual"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.WF.packCalls"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "assertion violation: fidx < fixedParamPerms.perms.size\n      "};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__3;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_packCalls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_packCalls___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_packCalls___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Not a forall: "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__1 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__1_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__2;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__3 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mutualName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_unary"};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_mutualName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mutualName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 103, 179, 87, 16, 42, 175, 175)}};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_mutualName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_mutual"};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__2_value;
static const lean_ctor_object l_Lean_Elab_WF_mutualName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mutualName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(60, 96, 167, 116, 153, 200, 47, 59)}};
static const lean_object* l_Lean_Elab_WF_mutualName___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mutualName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Elab.WF.varyingVarNames"};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: xs.size = arity\n    "};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2;
static const lean_string_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "assertion violation: fixedParamPerms.perms[preDefIdx]!.size = arity\n    "};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4;
static const lean_array_object l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_varyingVarNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_varyingVarNames___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_varyingVarNames___closed__0 = (const lean_object*)&l_Lean_Elab_WF_varyingVarNames___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.WF.preDefsFromUnaryNonRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: arity = params.size\n        "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(lean_object* v_type_19_, lean_object* v_maxFVars_x3f_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, uint8_t v_whnfType_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_29_, 0, v_k_21_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_19_, v_maxFVars_x3f_20_, v___f_29_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___boxed(lean_object* v_type_47_, lean_object* v_maxFVars_x3f_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_51_);
v_res_59_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_47_, v_maxFVars_x3f_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_maxFVars_x3f_62_, lean_object* v_k_63_, uint8_t v_cleanupAnnotations_64_, uint8_t v_whnfType_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_61_, v_maxFVars_x3f_62_, v_k_63_, v_cleanupAnnotations_64_, v_whnfType_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___boxed(lean_object* v_00_u03b1_72_, lean_object* v_type_73_, lean_object* v_maxFVars_x3f_74_, lean_object* v_k_75_, lean_object* v_cleanupAnnotations_76_, lean_object* v_whnfType_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_83_; uint8_t v_whnfType_boxed_84_; lean_object* v_res_85_; 
v_cleanupAnnotations_boxed_83_ = lean_unbox(v_cleanupAnnotations_76_);
v_whnfType_boxed_84_ = lean_unbox(v_whnfType_77_);
v_res_85_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1(v_00_u03b1_72_, v_type_73_, v_maxFVars_x3f_74_, v_k_75_, v_cleanupAnnotations_boxed_83_, v_whnfType_boxed_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(lean_object* v_msgData_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_88_);
v_mctx_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_94_);
v_lctx_96_ = lean_ctor_get(v___y_87_, 2);
v_options_97_ = lean_ctor_get(v___y_89_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_93_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_86_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_ref_114_ = lean_ctor_get(v___y_111_, 5);
v___x_115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
lean_inc(v_ref_114_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_ref_114_);
lean_ctor_set(v___x_120_, 1, v_a_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Elab_WF_withAppN___lam__0___closed__0));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object* v_args_135_, lean_object* v_k_136_, uint8_t v___x_137_, lean_object* v_missing_138_, lean_object* v_xs_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_array_get_size(v_xs_139_);
v___x_154_ = lean_nat_dec_lt(v___x_153_, v_missing_138_);
if (v___x_154_ == 0)
{
goto v___jp_146_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v_k_136_);
lean_dec_ref(v_args_135_);
v___x_155_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___lam__0___closed__1, &l_Lean_Elab_WF_withAppN___lam__0___closed__1_once, _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1);
v___x_156_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_155_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = l_Array_append___redArg(v_args_135_, v_xs_139_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v___x_148_ = lean_apply_6(v_k_136_, v___x_147_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, lean_box(0));
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; uint8_t v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = 1;
v___x_151_ = 1;
v___x_152_ = l_Lean_Meta_mkLambdaFVars(v_xs_139_, v_a_149_, v___x_137_, v___x_150_, v___x_137_, v___x_150_, v___x_151_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_152_;
}
else
{
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object* v_args_165_, lean_object* v_k_166_, lean_object* v___x_167_, lean_object* v_missing_168_, lean_object* v_xs_169_, lean_object* v_x_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v___x_2318__boxed_176_; lean_object* v_res_177_; 
v___x_2318__boxed_176_ = lean_unbox(v___x_167_);
v_res_177_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_165_, v_k_166_, v___x_2318__boxed_176_, v_missing_168_, v_xs_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v_x_170_);
lean_dec_ref(v_xs_169_);
lean_dec(v_missing_168_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___closed__0(void){
_start:
{
lean_object* v___x_178_; lean_object* v_dummy_179_; 
v___x_178_ = lean_box(0);
v_dummy_179_ = l_Lean_Expr_sort___override(v___x_178_);
return v_dummy_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN(lean_object* v_n_180_, lean_object* v_e_181_, lean_object* v_k_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_dummy_188_; lean_object* v_nargs_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_args_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_dummy_188_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_189_ = l_Lean_Expr_getAppNumArgs(v_e_181_);
lean_inc(v_nargs_189_);
v___x_190_ = lean_mk_array(v_nargs_189_, v_dummy_188_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_sub(v_nargs_189_, v___x_191_);
lean_dec(v_nargs_189_);
lean_inc_ref(v_e_181_);
v_args_193_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_181_, v___x_190_, v___x_192_);
v___x_194_ = lean_array_get_size(v_args_193_);
v___x_195_ = lean_nat_dec_le(v_n_180_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
v___x_196_ = lean_infer_type(v_e_181_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_missing_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_205_; 
v_missing_201_ = lean_nat_sub(v_n_180_, v___x_194_);
lean_dec(v_n_180_);
v___x_202_ = lean_box(v___x_195_);
lean_inc(v_missing_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_withAppN___lam__0___boxed), 11, 4);
lean_closure_set(v___f_203_, 0, v_args_193_);
lean_closure_set(v___f_203_, 1, v_k_182_);
lean_closure_set(v___f_203_, 2, v___x_202_);
lean_closure_set(v___f_203_, 3, v_missing_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 1);
lean_ctor_set(v___x_199_, 0, v_missing_201_);
v___x_205_ = v___x_199_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_missing_201_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_a_197_, v___x_205_, v___f_203_, v___x_195_, v___x_195_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v___x_206_;
}
}
}
else
{
lean_dec_ref(v_args_193_);
lean_dec_ref(v_k_182_);
lean_dec(v_n_180_);
return v___x_196_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v_e_181_);
v___x_209_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_180_);
lean_inc_ref(v_args_193_);
v___x_210_ = l_Array_toSubarray___redArg(v_args_193_, v___x_209_, v_n_180_);
v___x_211_ = l_Subarray_copy___redArg(v___x_210_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
v___x_212_ = lean_apply_6(v_k_182_, v___x_211_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_227_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_227_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_lower_218_; lean_object* v_upper_219_; uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_le(v_n_180_, v___x_209_);
if (v___x_226_ == 0)
{
v_lower_218_ = v_n_180_;
v_upper_219_ = v___x_194_;
goto v___jp_217_;
}
else
{
lean_dec(v_n_180_);
v_lower_218_ = v___x_209_;
v_upper_219_ = v___x_194_;
goto v___jp_217_;
}
v___jp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_220_ = l_Array_toSubarray___redArg(v_args_193_, v_lower_218_, v_upper_219_);
v___x_221_ = l_Subarray_copy___redArg(v___x_220_);
v___x_222_ = l_Lean_mkAppN(v_a_213_, v___x_221_);
lean_dec_ref(v___x_221_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_222_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_dec_ref(v_args_193_);
lean_dec(v_n_180_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object* v_n_228_, lean_object* v_e_229_, lean_object* v_k_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Elab_WF_withAppN(v_n_228_, v_e_229_, v_k_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object* v_00_u03b1_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object* v_00_u03b1_245_, lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(v_00_u03b1_245_, v_msg_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___f_260_; lean_object* v___x_1447__overap_261_; lean_object* v___x_262_; 
v___f_260_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1447__overap_261_ = lean_panic_fn_borrowed(v___f_260_, v_msg_254_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_262_ = lean_apply_5(v___x_1447__overap_261_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__0___closed__0));
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_WF_packCalls___lam__0(v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec_ref(v_x_280_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object* v___x_287_, lean_object* v_argsPacker_288_, lean_object* v___x_289_, lean_object* v_val_290_, lean_object* v_newF_291_, lean_object* v_args_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_287_, v_args_292_);
v___x_299_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_288_, v___x_289_, v_val_290_, v___x_298_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec_ref(v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = l_Lean_Expr_app___override(v_newF_291_, v_a_300_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_dec_ref(v_newF_291_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object* v___x_309_, lean_object* v_argsPacker_310_, lean_object* v___x_311_, lean_object* v_val_312_, lean_object* v_newF_313_, lean_object* v_args_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Elab_WF_packCalls___lam__1(v___x_309_, v_argsPacker_310_, v___x_311_, v_val_312_, v_newF_313_, v_args_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec_ref(v_args_314_);
lean_dec_ref(v_argsPacker_310_);
lean_dec_ref(v___x_309_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object* v_xs_321_, lean_object* v_v_322_, lean_object* v_i_323_){
_start:
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_get_size(v_xs_321_);
v___x_325_ = lean_nat_dec_lt(v_i_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_i_323_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_fget_borrowed(v_xs_321_, v_i_323_);
v___x_328_ = lean_name_eq(v___x_327_, v_v_322_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_add(v_i_323_, v___x_329_);
lean_dec(v_i_323_);
v_i_323_ = v___x_330_;
goto _start;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v_i_323_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_333_, lean_object* v_v_334_, lean_object* v_i_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_333_, v_v_334_, v_i_335_);
lean_dec(v_v_334_);
lean_dec_ref(v_xs_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object* v_xs_337_, lean_object* v_v_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_337_, v_v_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object* v_xs_341_, lean_object* v_v_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_341_, v_v_342_);
lean_dec(v_v_342_);
lean_dec_ref(v_xs_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object* v_xs_344_, lean_object* v_v_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_344_, v_v_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_val_348_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_346_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_val_348_);
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
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object* v_xs_356_, lean_object* v_v_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_xs_356_, v_v_357_);
lean_dec(v_v_357_);
lean_dec_ref(v_xs_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(uint8_t v___x_359_, size_t v_sz_360_, size_t v_i_361_, lean_object* v_bs_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_361_, v_sz_360_);
if (v___x_363_ == 0)
{
return v_bs_362_;
}
else
{
lean_object* v_v_364_; lean_object* v___x_365_; lean_object* v_bs_x27_366_; uint8_t v___y_368_; 
v_v_364_ = lean_array_uget(v_bs_362_, v_i_361_);
v___x_365_ = lean_unsigned_to_nat(0u);
v_bs_x27_366_ = lean_array_uset(v_bs_362_, v_i_361_, v___x_365_);
if (lean_obj_tag(v_v_364_) == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 0;
v___y_368_ = v___x_374_;
goto v___jp_367_;
}
else
{
lean_dec_ref_known(v_v_364_, 1);
v___y_368_ = v___x_359_;
goto v___jp_367_;
}
v___jp_367_:
{
size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_361_, v___x_369_);
v___x_371_ = lean_box(v___y_368_);
v___x_372_ = lean_array_uset(v_bs_x27_366_, v_i_361_, v___x_371_);
v_i_361_ = v___x_370_;
v_bs_362_ = v___x_372_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object* v___x_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_bs_378_){
_start:
{
uint8_t v___x_10921__boxed_379_; size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v___x_10921__boxed_379_ = lean_unbox(v___x_375_);
v_sz_boxed_380_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_381_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_10921__boxed_379_, v_sz_boxed_380_, v_i_boxed_381_, v_bs_378_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_386_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__2));
v___x_387_ = lean_unsigned_to_nat(6u);
v___x_388_ = lean_unsigned_to_nat(55u);
v___x_389_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__1));
v___x_390_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_391_ = l_mkPanicMessageWithDecl(v___x_390_, v___x_389_, v___x_388_, v___x_387_, v___x_386_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Array_instInhabited(lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object* v_funNames_393_, lean_object* v_fixedParamPerms_394_, lean_object* v_argsPacker_395_, lean_object* v___x_396_, lean_object* v_newF_397_, lean_object* v_e_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = l_Lean_Expr_getAppFn(v_e_398_);
v___x_405_ = l_Lean_Expr_isConst(v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___x_404_);
lean_dec_ref(v_newF_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_argsPacker_395_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_e_398_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l_Lean_Expr_constName_x21(v___x_404_);
lean_dec_ref(v___x_404_);
v___x_409_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_funNames_393_, v___x_408_);
lean_dec(v___x_408_);
if (lean_obj_tag(v___x_409_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_446_; 
v_val_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_446_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_446_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_446_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_perms_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_perms_414_ = lean_ctor_get(v_fixedParamPerms_394_, 1);
v___x_415_ = lean_array_get_size(v_perms_414_);
v___x_416_ = lean_nat_dec_lt(v_val_410_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_del_object(v___x_412_);
lean_dec(v_val_410_);
lean_dec_ref(v_e_398_);
lean_dec_ref(v_newF_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_argsPacker_395_);
v___x_417_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__3, &l_Lean_Elab_WF_packCalls___lam__2___closed__3_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3);
v___x_418_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v___x_417_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; size_t v_sz_422_; size_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_419_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_420_ = lean_array_get_borrowed(v___x_419_, v_perms_414_, v_val_410_);
lean_inc_n(v___x_420_, 2);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_421_, 0, v___x_420_);
lean_closure_set(v___f_421_, 1, v_argsPacker_395_);
lean_closure_set(v___f_421_, 2, v___x_396_);
lean_closure_set(v___f_421_, 3, v_val_410_);
lean_closure_set(v___f_421_, 4, v_newF_397_);
v_sz_422_ = lean_array_size(v___x_420_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_405_, v_sz_422_, v___x_423_, v___x_420_);
v___x_425_ = lean_array_get_size(v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = l_Lean_Elab_WF_withAppN(v___x_425_, v_e_398_, v___f_421_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_437_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_437_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_437_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 0);
lean_ctor_set(v___x_412_, 0, v_a_427_);
v___x_432_ = v___x_412_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_412_);
v_a_438_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_426_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_426_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_409_);
lean_dec_ref(v_newF_397_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_argsPacker_395_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_e_398_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object* v_funNames_449_, lean_object* v_fixedParamPerms_450_, lean_object* v_argsPacker_451_, lean_object* v___x_452_, lean_object* v_newF_453_, lean_object* v_e_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Elab_WF_packCalls___lam__2(v_funNames_449_, v_fixedParamPerms_450_, v_argsPacker_451_, v___x_452_, v_newF_453_, v_e_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_fixedParamPerms_450_);
lean_dec_ref(v_funNames_449_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object* v_00_u03b1_461_, lean_object* v_x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_apply_1(v_x_462_, lean_box(0));
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object* v_00_u03b1_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(v_00_u03b1_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_478_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_492_, lean_object* v___y_493_, lean_object* v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_493_);
v___x_500_ = lean_apply_7(v_k_492_, v_b_494_, v___y_493_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, lean_box(0));
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_501_, lean_object* v___y_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_501_, v___y_502_, v_b_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_510_, lean_object* v_type_511_, lean_object* v_val_512_, lean_object* v_k_513_, uint8_t v_nondep_514_, uint8_t v_kind_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___f_522_; lean_object* v___x_523_; 
lean_inc(v___y_516_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_522_, 0, v_k_513_);
lean_closure_set(v___f_522_, 1, v___y_516_);
v___x_523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_510_, v_type_511_, v_val_512_, v___f_522_, v_nondep_514_, v_kind_515_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_523_) == 0)
{
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_532_, lean_object* v_type_533_, lean_object* v_val_534_, lean_object* v_k_535_, lean_object* v_nondep_536_, lean_object* v_kind_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
uint8_t v_nondep_boxed_544_; uint8_t v_kind_boxed_545_; lean_object* v_res_546_; 
v_nondep_boxed_544_ = lean_unbox(v_nondep_536_);
v_kind_boxed_545_ = lean_unbox(v_kind_537_);
v_res_546_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_532_, v_type_533_, v_val_534_, v_k_535_, v_nondep_boxed_544_, v_kind_boxed_545_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_547_, uint8_t v_bi_548_, lean_object* v_type_549_, lean_object* v_k_550_, uint8_t v_kind_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___f_558_; lean_object* v___x_559_; 
lean_inc(v___y_552_);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_558_, 0, v_k_550_);
lean_closure_set(v___f_558_, 1, v___y_552_);
v___x_559_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_547_, v_bi_548_, v_type_549_, v___f_558_, v_kind_551_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_559_) == 0)
{
return v___x_559_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_568_, lean_object* v_bi_569_, lean_object* v_type_570_, lean_object* v_k_571_, lean_object* v_kind_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_bi_boxed_579_; uint8_t v_kind_boxed_580_; lean_object* v_res_581_; 
v_bi_boxed_579_ = lean_unbox(v_bi_569_);
v_kind_boxed_580_ = lean_unbox(v_kind_572_);
v_res_581_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_568_, v_bi_boxed_579_, v_type_570_, v_k_571_, v_kind_boxed_580_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_apply_1(v_x_583_, lean_box(0));
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_591_, lean_object* v_x_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_591_, v_x_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lean_maxRecDepthErrorMessage;
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
v___x_607_ = l_Lean_MessageData_ofFormat(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
v___x_609_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2));
v___x_610_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object* v_ref_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_ref_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object* v_ref_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object* v_x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___y_627_; lean_object* v_fileName_636_; lean_object* v_fileMap_637_; lean_object* v_options_638_; lean_object* v_currRecDepth_639_; lean_object* v_maxRecDepth_640_; lean_object* v_ref_641_; lean_object* v_currNamespace_642_; lean_object* v_openDecls_643_; lean_object* v_initHeartbeats_644_; lean_object* v_maxHeartbeats_645_; lean_object* v_quotContext_646_; lean_object* v_currMacroScope_647_; uint8_t v_diag_648_; lean_object* v_cancelTk_x3f_649_; uint8_t v_suppressElabErrors_650_; lean_object* v_inheritedTraceOptions_651_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_fileName_636_ = lean_ctor_get(v___y_623_, 0);
v_fileMap_637_ = lean_ctor_get(v___y_623_, 1);
v_options_638_ = lean_ctor_get(v___y_623_, 2);
v_currRecDepth_639_ = lean_ctor_get(v___y_623_, 3);
v_maxRecDepth_640_ = lean_ctor_get(v___y_623_, 4);
v_ref_641_ = lean_ctor_get(v___y_623_, 5);
v_currNamespace_642_ = lean_ctor_get(v___y_623_, 6);
v_openDecls_643_ = lean_ctor_get(v___y_623_, 7);
v_initHeartbeats_644_ = lean_ctor_get(v___y_623_, 8);
v_maxHeartbeats_645_ = lean_ctor_get(v___y_623_, 9);
v_quotContext_646_ = lean_ctor_get(v___y_623_, 10);
v_currMacroScope_647_ = lean_ctor_get(v___y_623_, 11);
v_diag_648_ = lean_ctor_get_uint8(v___y_623_, sizeof(void*)*14);
v_cancelTk_x3f_649_ = lean_ctor_get(v___y_623_, 12);
v_suppressElabErrors_650_ = lean_ctor_get_uint8(v___y_623_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_651_ = lean_ctor_get(v___y_623_, 13);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_eq(v_maxRecDepth_640_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = lean_nat_dec_eq(v_currRecDepth_639_, v_maxRecDepth_640_);
if (v___x_659_ == 0)
{
goto v___jp_652_;
}
else
{
lean_object* v___x_660_; 
lean_dec_ref(v_x_619_);
lean_inc(v_ref_641_);
v___x_660_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_641_);
v___y_627_ = v___x_660_;
goto v___jp_626_;
}
}
else
{
goto v___jp_652_;
}
v___jp_626_:
{
if (lean_obj_tag(v___y_627_) == 0)
{
return v___y_627_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
v_a_628_ = lean_ctor_get(v___y_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___y_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___y_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
v___jp_652_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_currRecDepth_639_, v___x_653_);
lean_inc_ref(v_inheritedTraceOptions_651_);
lean_inc(v_cancelTk_x3f_649_);
lean_inc(v_currMacroScope_647_);
lean_inc(v_quotContext_646_);
lean_inc(v_maxHeartbeats_645_);
lean_inc(v_initHeartbeats_644_);
lean_inc(v_openDecls_643_);
lean_inc(v_currNamespace_642_);
lean_inc(v_ref_641_);
lean_inc(v_maxRecDepth_640_);
lean_inc_ref(v_options_638_);
lean_inc_ref(v_fileMap_637_);
lean_inc_ref(v_fileName_636_);
v___x_655_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_655_, 0, v_fileName_636_);
lean_ctor_set(v___x_655_, 1, v_fileMap_637_);
lean_ctor_set(v___x_655_, 2, v_options_638_);
lean_ctor_set(v___x_655_, 3, v___x_654_);
lean_ctor_set(v___x_655_, 4, v_maxRecDepth_640_);
lean_ctor_set(v___x_655_, 5, v_ref_641_);
lean_ctor_set(v___x_655_, 6, v_currNamespace_642_);
lean_ctor_set(v___x_655_, 7, v_openDecls_643_);
lean_ctor_set(v___x_655_, 8, v_initHeartbeats_644_);
lean_ctor_set(v___x_655_, 9, v_maxHeartbeats_645_);
lean_ctor_set(v___x_655_, 10, v_quotContext_646_);
lean_ctor_set(v___x_655_, 11, v_currMacroScope_647_);
lean_ctor_set(v___x_655_, 12, v_cancelTk_x3f_649_);
lean_ctor_set(v___x_655_, 13, v_inheritedTraceOptions_651_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*14, v_diag_648_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*14 + 1, v_suppressElabErrors_650_);
lean_inc(v___y_624_);
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v___y_620_);
v___x_656_ = lean_apply_6(v_x_619_, v___y_620_, v___y_621_, v___y_622_, v___x_655_, v___y_624_, lean_box(0));
v___y_627_ = v___x_656_;
goto v___jp_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_m_669_, lean_object* v_query_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v_zero_674_; uint8_t v_isZero_675_; 
v_zero_674_ = lean_unsigned_to_nat(0u);
v_isZero_675_ = lean_nat_dec_eq(v_x_672_, v_zero_674_);
if (v_isZero_675_ == 1)
{
lean_dec(v_x_673_);
lean_dec(v_x_672_);
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_box(2);
return v___x_676_;
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_val_677_ = lean_ctor_get(v_x_671_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v_x_671_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v_x_671_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_val_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_keyArray_685_; lean_object* v_valueArray_686_; lean_object* v___x_687_; uint8_t v_isSome_688_; 
v_keyArray_685_ = lean_ctor_get(v_m_669_, 1);
v_valueArray_686_ = lean_ctor_get(v_m_669_, 2);
v___x_687_ = lean_array_fget_borrowed(v_keyArray_685_, v_x_673_);
v_isSome_688_ = lean_noption_is_some(v___x_687_);
if (v_isSome_688_ == 0)
{
lean_dec(v_x_672_);
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_x_673_);
return v___x_689_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_x_673_);
v_val_690_ = lean_ctor_get(v_x_671_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v_x_671_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v_x_671_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_val_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_one_698_; lean_object* v_n_699_; lean_object* v___y_701_; 
v_one_698_ = lean_unsigned_to_nat(1u);
v_n_699_ = lean_nat_sub(v_x_672_, v_one_698_);
lean_dec(v_x_672_);
if (v_isSome_688_ == 0)
{
goto v___jp_707_;
}
else
{
lean_object* v___x_709_; uint8_t v_isSome_710_; 
v___x_709_ = lean_array_fget_borrowed(v_valueArray_686_, v_x_673_);
v_isSome_710_ = lean_noption_is_some(v___x_709_);
if (v_isSome_710_ == 0)
{
goto v___jp_707_;
}
else
{
lean_object* v_val_711_; uint8_t v___x_712_; 
lean_inc(v___x_687_);
v_val_711_ = lean_noption_get(v___x_687_);
v___x_712_ = l_Lean_ExprStructEq_beq(v_val_711_, v_query_670_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
lean_dec(v_val_711_);
v___x_713_ = lean_array_get_size(v_keyArray_685_);
v___x_714_ = lean_nat_add(v_x_673_, v_one_698_);
lean_dec(v_x_673_);
v___x_715_ = lean_nat_dec_lt(v___x_714_, v___x_713_);
if (v___x_715_ == 0)
{
lean_dec(v___x_714_);
v_x_672_ = v_n_699_;
v_x_673_ = v_zero_674_;
goto _start;
}
else
{
v_x_672_ = v_n_699_;
v_x_673_ = v___x_714_;
goto _start;
}
}
else
{
lean_object* v_val_718_; lean_object* v___x_719_; 
lean_dec(v_n_699_);
lean_dec(v_x_671_);
lean_inc(v___x_709_);
v_val_718_ = lean_noption_get(v___x_709_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_x_673_);
lean_ctor_set(v___x_719_, 1, v_val_711_);
lean_ctor_set(v___x_719_, 2, v_val_718_);
return v___x_719_;
}
}
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_array_get_size(v_keyArray_685_);
v___x_703_ = lean_nat_add(v_x_673_, v_one_698_);
lean_dec(v_x_673_);
v___x_704_ = lean_nat_dec_lt(v___x_703_, v___x_702_);
if (v___x_704_ == 0)
{
lean_dec(v___x_703_);
v_x_671_ = v___y_701_;
v_x_672_ = v_n_699_;
v_x_673_ = v_zero_674_;
goto _start;
}
else
{
v_x_671_ = v___y_701_;
v_x_672_ = v_n_699_;
v_x_673_ = v___x_703_;
goto _start;
}
}
v___jp_707_:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_708_; 
lean_inc(v_x_673_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_x_673_);
v___y_701_ = v___x_708_;
goto v___jp_700_;
}
else
{
v___y_701_ = v_x_671_;
goto v___jp_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_m_720_, lean_object* v_query_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_m_720_, v_query_721_, v_x_722_, v_x_723_, v_x_724_);
lean_dec_ref(v_query_721_);
lean_dec_ref(v_m_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_726_, lean_object* v_query_727_){
_start:
{
lean_object* v_keyArray_728_; lean_object* v___x_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; uint64_t v_fold_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; size_t v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_keyArray_728_ = lean_ctor_get(v_m_726_, 1);
v___x_729_ = lean_array_get_size(v_keyArray_728_);
v___x_730_ = l_Lean_ExprStructEq_hash(v_query_727_);
v___x_731_ = 32ULL;
v___x_732_ = lean_uint64_shift_right(v___x_730_, v___x_731_);
v_fold_733_ = lean_uint64_xor(v___x_730_, v___x_732_);
v___x_734_ = 16ULL;
v___x_735_ = lean_uint64_shift_right(v_fold_733_, v___x_734_);
v___x_736_ = lean_uint64_xor(v_fold_733_, v___x_735_);
v___x_737_ = lean_uint64_to_usize(v___x_736_);
v___x_738_ = lean_usize_of_nat(v___x_729_);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_sub(v___x_738_, v___x_739_);
v___x_741_ = lean_usize_land(v___x_737_, v___x_740_);
v___x_742_ = lean_usize_to_nat(v___x_741_);
v___x_743_ = lean_box(0);
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_m_726_, v_query_727_, v___x_743_, v___x_729_, v___x_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg___boxed(lean_object* v_m_745_, lean_object* v_query_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_745_, v_query_746_);
lean_dec_ref(v_query_746_);
lean_dec_ref(v_m_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_m_748_, lean_object* v_query_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_748_, v_query_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_index_751_; lean_object* v_key_752_; lean_object* v_value_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_index_751_ = lean_ctor_get(v___x_750_, 0);
v_key_752_ = lean_ctor_get(v___x_750_, 1);
v_value_753_ = lean_ctor_get(v___x_750_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_750_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_value_753_);
lean_inc(v_key_752_);
lean_inc(v_index_751_);
lean_dec(v___x_750_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_index_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_key_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_value_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v___x_750_);
v___x_761_ = lean_box(1);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_m_762_, lean_object* v_query_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_m_762_, v_query_763_);
lean_dec_ref(v_query_763_);
lean_dec_ref(v_m_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_m_765_, v_a_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_value_768_; lean_object* v___x_769_; 
v_value_768_ = lean_ctor_get(v___x_767_, 2);
lean_inc(v_value_768_);
lean_dec_ref_known(v___x_767_, 3);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_value_768_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; 
v___x_770_ = lean_box(0);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_771_, v_a_772_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v_m_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg(lean_object* v_b_774_, lean_object* v_acc_775_, lean_object* v_i_776_){
_start:
{
lean_object* v___y_778_; lean_object* v_keyArray_786_; lean_object* v_valueArray_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_keyArray_786_ = lean_ctor_get(v_b_774_, 1);
v_valueArray_787_ = lean_ctor_get(v_b_774_, 2);
v___x_788_ = lean_array_get_size(v_keyArray_786_);
v___x_789_ = lean_nat_dec_lt(v_i_776_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_i_776_);
return v_acc_775_;
}
else
{
lean_object* v___x_790_; uint8_t v_isSome_791_; 
v___x_790_ = lean_array_fget_borrowed(v_keyArray_786_, v_i_776_);
v_isSome_791_ = lean_noption_is_some(v___x_790_);
if (v_isSome_791_ == 0)
{
goto v___jp_782_;
}
else
{
lean_object* v___x_792_; uint8_t v_isSome_793_; 
v___x_792_ = lean_array_fget_borrowed(v_valueArray_787_, v_i_776_);
v_isSome_793_ = lean_noption_is_some(v___x_792_);
if (v_isSome_793_ == 0)
{
goto v___jp_782_;
}
else
{
lean_object* v_val_794_; lean_object* v_val_795_; lean_object* v_i_797_; lean_object* v___x_802_; 
lean_inc(v___x_790_);
v_val_794_ = lean_noption_get(v___x_790_);
lean_inc(v___x_792_);
v_val_795_ = lean_noption_get(v___x_792_);
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_acc_775_, v_val_794_);
switch(lean_obj_tag(v___x_802_))
{
case 0:
{
lean_object* v_index_803_; lean_object* v_size_804_; lean_object* v___x_805_; 
v_index_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_index_803_);
lean_dec_ref_known(v___x_802_, 3);
v_size_804_ = lean_ctor_get(v_acc_775_, 0);
lean_inc(v_size_804_);
v___x_805_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_775_, v_size_804_, v_index_803_, v_val_794_, v_val_795_);
lean_dec(v_index_803_);
v___y_778_ = v___x_805_;
goto v___jp_777_;
}
case 1:
{
lean_object* v_index_806_; 
v_index_806_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_index_806_);
lean_dec_ref_known(v___x_802_, 1);
v_i_797_ = v_index_806_;
goto v___jp_796_;
}
default: 
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_775_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_index_809_; 
v_index_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_index_809_);
lean_dec_ref_known(v___x_808_, 1);
v_i_797_ = v_index_809_;
goto v___jp_796_;
}
else
{
lean_dec(v_val_795_);
lean_dec(v_val_794_);
v___y_778_ = v_acc_775_;
goto v___jp_777_;
}
}
}
v___jp_796_:
{
lean_object* v_size_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_size_798_ = lean_ctor_get(v_acc_775_, 0);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_size_798_, v___x_799_);
v___x_801_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_775_, v___x_800_, v_i_797_, v_val_794_, v_val_795_);
lean_dec(v_i_797_);
v___y_778_ = v___x_801_;
goto v___jp_777_;
}
}
}
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_i_776_, v___x_779_);
lean_dec(v_i_776_);
v_acc_775_ = v___y_778_;
v_i_776_ = v___x_780_;
goto _start;
}
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_i_776_, v___x_783_);
lean_dec(v_i_776_);
v_i_776_ = v___x_784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg___boxed(lean_object* v_b_810_, lean_object* v_acc_811_, lean_object* v_i_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg(v_b_810_, v_acc_811_, v_i_812_);
lean_dec_ref(v_b_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg(lean_object* v_init_814_, lean_object* v_b_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg(v_b_815_, v_init_814_, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg___boxed(lean_object* v_init_818_, lean_object* v_b_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg(v_init_818_, v_b_819_);
lean_dec_ref(v_b_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(lean_object* v_m_821_){
_start:
{
lean_object* v_keyArray_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_cellCount_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_target_829_; lean_object* v___x_830_; 
v_keyArray_822_ = lean_ctor_get(v_m_821_, 1);
v___x_823_ = lean_array_get_size(v_keyArray_822_);
v___x_824_ = lean_unsigned_to_nat(2u);
v_cellCount_825_ = lean_nat_mul(v___x_823_, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_825_);
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_825_);
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_825_);
v_target_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_829_, 0, v___x_826_);
lean_ctor_set(v_target_829_, 1, v___x_827_);
lean_ctor_set(v_target_829_, 2, v___x_828_);
v___x_830_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg(v_target_829_, v_m_821_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg___boxed(lean_object* v_m_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(v_m_831_);
lean_dec_ref(v_m_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_833_, lean_object* v_e_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___y_840_; lean_object* v___y_843_; lean_object* v_i_844_; lean_object* v___y_860_; lean_object* v_i_861_; lean_object* v___y_867_; lean_object* v___x_876_; 
v___x_837_ = lean_st_ref_take(v_a_833_);
v___x_838_ = lean_box(0);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_837_, v_e_834_);
switch(lean_obj_tag(v___x_876_))
{
case 0:
{
lean_object* v_index_877_; lean_object* v_size_878_; lean_object* v___x_879_; 
v_index_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_index_877_);
lean_dec_ref_known(v___x_876_, 3);
v_size_878_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_size_878_);
v___x_879_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_837_, v_size_878_, v_index_877_, v_e_834_, v_a_835_);
lean_dec(v_index_877_);
v___y_840_ = v___x_879_;
goto v___jp_839_;
}
case 1:
{
lean_object* v_index_880_; lean_object* v_size_881_; lean_object* v_keyArray_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_index_880_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_index_880_);
lean_dec_ref_known(v___x_876_, 1);
v_size_881_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_size_881_);
v_keyArray_882_ = lean_ctor_get(v___x_837_, 1);
lean_inc_ref(v_keyArray_882_);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_add(v_size_881_, v___x_883_);
lean_dec(v_size_881_);
v___x_885_ = lean_array_get_size(v_keyArray_882_);
lean_dec_ref(v_keyArray_882_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_dec(v___x_884_);
lean_dec(v_index_880_);
goto v___jp_849_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_887_ = lean_unsigned_to_nat(4u);
v___x_888_ = lean_nat_mul(v___x_884_, v___x_887_);
v___x_889_ = lean_unsigned_to_nat(3u);
v___x_890_ = lean_nat_mul(v___x_885_, v___x_889_);
v___x_891_ = lean_nat_dec_le(v___x_888_, v___x_890_);
lean_dec(v___x_890_);
lean_dec(v___x_888_);
if (v___x_891_ == 0)
{
lean_dec(v___x_884_);
lean_dec(v_index_880_);
goto v___jp_849_;
}
else
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_837_, v___x_884_, v_index_880_, v_e_834_, v_a_835_);
lean_dec(v_index_880_);
v___y_840_ = v___x_892_;
goto v___jp_839_;
}
}
}
default: 
{
lean_object* v_size_893_; lean_object* v_keyArray_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_size_893_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_size_893_);
v_keyArray_894_ = lean_ctor_get(v___x_837_, 1);
lean_inc_ref(v_keyArray_894_);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_add(v_size_893_, v___x_895_);
lean_dec(v_size_893_);
v___x_897_ = lean_array_get_size(v_keyArray_894_);
lean_dec_ref(v_keyArray_894_);
v___x_898_ = lean_nat_dec_lt(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec(v___x_896_);
v___x_899_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(v___x_837_);
lean_dec(v___x_837_);
v___y_867_ = v___x_899_;
goto v___jp_866_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_900_ = lean_unsigned_to_nat(4u);
v___x_901_ = lean_nat_mul(v___x_896_, v___x_900_);
lean_dec(v___x_896_);
v___x_902_ = lean_unsigned_to_nat(3u);
v___x_903_ = lean_nat_mul(v___x_897_, v___x_902_);
v___x_904_ = lean_nat_dec_le(v___x_901_, v___x_903_);
lean_dec(v___x_903_);
lean_dec(v___x_901_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(v___x_837_);
lean_dec(v___x_837_);
v___y_867_ = v___x_905_;
goto v___jp_866_;
}
else
{
v___y_867_ = v___x_837_;
goto v___jp_866_;
}
}
}
}
v___jp_839_:
{
lean_object* v___x_841_; 
v___x_841_ = lean_st_ref_put(v_a_833_, v___y_840_);
return v___x_838_;
}
v___jp_842_:
{
lean_object* v_size_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_size_845_ = lean_ctor_get(v___y_843_, 0);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_add(v_size_845_, v___x_846_);
v___x_848_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_843_, v___x_847_, v_i_844_, v_e_834_, v_a_835_);
lean_dec(v_i_844_);
v___y_840_ = v___x_848_;
goto v___jp_839_;
}
v___jp_849_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(v___x_837_);
lean_dec(v___x_837_);
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_850_, v_e_834_);
switch(lean_obj_tag(v___x_851_))
{
case 0:
{
lean_object* v_index_852_; lean_object* v_size_853_; lean_object* v___x_854_; 
v_index_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_index_852_);
lean_dec_ref_known(v___x_851_, 3);
v_size_853_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_size_853_);
v___x_854_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_850_, v_size_853_, v_index_852_, v_e_834_, v_a_835_);
lean_dec(v_index_852_);
v___y_840_ = v___x_854_;
goto v___jp_839_;
}
case 1:
{
lean_object* v_index_855_; 
v_index_855_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_index_855_);
lean_dec_ref_known(v___x_851_, 1);
v___y_843_ = v___x_850_;
v_i_844_ = v_index_855_;
goto v___jp_842_;
}
default: 
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_850_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_index_858_; 
v_index_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_index_858_);
lean_dec_ref_known(v___x_857_, 1);
v___y_843_ = v___x_850_;
v_i_844_ = v_index_858_;
goto v___jp_842_;
}
else
{
lean_dec_ref(v_a_835_);
lean_dec_ref(v_e_834_);
v___y_840_ = v___x_850_;
goto v___jp_839_;
}
}
}
}
v___jp_859_:
{
lean_object* v_size_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_size_862_ = lean_ctor_get(v___y_860_, 0);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_add(v_size_862_, v___x_863_);
v___x_865_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_860_, v___x_864_, v_i_861_, v_e_834_, v_a_835_);
lean_dec(v_i_861_);
v___y_840_ = v___x_865_;
goto v___jp_839_;
}
v___jp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___y_867_, v_e_834_);
switch(lean_obj_tag(v___x_868_))
{
case 0:
{
lean_object* v_index_869_; lean_object* v_size_870_; lean_object* v___x_871_; 
v_index_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_index_869_);
lean_dec_ref_known(v___x_868_, 3);
v_size_870_ = lean_ctor_get(v___y_867_, 0);
lean_inc(v_size_870_);
v___x_871_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_867_, v_size_870_, v_index_869_, v_e_834_, v_a_835_);
lean_dec(v_index_869_);
v___y_840_ = v___x_871_;
goto v___jp_839_;
}
case 1:
{
lean_object* v_index_872_; 
v_index_872_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_index_872_);
lean_dec_ref_known(v___x_868_, 1);
v___y_860_ = v___y_867_;
v_i_861_ = v_index_872_;
goto v___jp_859_;
}
default: 
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_867_, v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_index_875_; 
v_index_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_index_875_);
lean_dec_ref_known(v___x_874_, 1);
v___y_860_ = v___y_867_;
v_i_861_ = v_index_875_;
goto v___jp_859_;
}
else
{
lean_dec_ref(v_a_835_);
lean_dec_ref(v_e_834_);
v___y_840_ = v___y_867_;
goto v___jp_839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_906_, lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_906_, v_e_907_, v_a_908_);
lean_dec(v_a_906_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_914_, lean_object* v_pre_915_, lean_object* v_post_916_, uint8_t v_usedLetOnly_917_, uint8_t v_skipConstInApp_918_, uint8_t v_skipInstances_919_, lean_object* v_body_920_, lean_object* v_x_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_array_push(v_fvars_914_, v_x_921_);
v___x_929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_915_, v_post_916_, v_usedLetOnly_917_, v_skipConstInApp_918_, v_skipInstances_919_, v___x_928_, v_body_920_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_930_, lean_object* v_pre_931_, lean_object* v_post_932_, lean_object* v_usedLetOnly_933_, lean_object* v_skipConstInApp_934_, lean_object* v_skipInstances_935_, lean_object* v_body_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v_usedLetOnly_boxed_944_; uint8_t v_skipConstInApp_boxed_945_; uint8_t v_skipInstances_boxed_946_; lean_object* v_res_947_; 
v_usedLetOnly_boxed_944_ = lean_unbox(v_usedLetOnly_933_);
v_skipConstInApp_boxed_945_ = lean_unbox(v_skipConstInApp_934_);
v_skipInstances_boxed_946_ = lean_unbox(v_skipInstances_935_);
v_res_947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_930_, v_pre_931_, v_post_932_, v_usedLetOnly_boxed_944_, v_skipConstInApp_boxed_945_, v_skipInstances_boxed_946_, v_body_936_, v_x_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_948_, lean_object* v_post_949_, uint8_t v_usedLetOnly_950_, uint8_t v_skipConstInApp_951_, uint8_t v_skipInstances_952_, lean_object* v_e_953_, lean_object* v_a_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; 
lean_inc_ref(v_post_949_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc_ref(v___y_955_);
lean_inc_ref(v_e_953_);
v___x_960_ = lean_apply_6(v_post_949_, v_e_953_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, lean_box(0));
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_979_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
switch(lean_obj_tag(v_a_961_))
{
case 0:
{
lean_object* v_e_965_; lean_object* v___x_967_; 
lean_dec_ref(v_e_953_);
lean_dec_ref(v_post_949_);
lean_dec_ref(v_pre_948_);
v_e_965_ = lean_ctor_get(v_a_961_, 0);
lean_inc_ref(v_e_965_);
lean_dec_ref_known(v_a_961_, 1);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_e_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_e_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
case 1:
{
lean_object* v_e_969_; lean_object* v___x_970_; 
lean_del_object(v___x_963_);
lean_dec_ref(v_e_953_);
v_e_969_ = lean_ctor_get(v_a_961_, 0);
lean_inc_ref(v_e_969_);
lean_dec_ref_known(v_a_961_, 1);
v___x_970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_948_, v_post_949_, v_usedLetOnly_950_, v_skipConstInApp_951_, v_skipInstances_952_, v_e_969_, v_a_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_970_;
}
default: 
{
lean_object* v_e_x3f_971_; 
lean_dec_ref(v_post_949_);
lean_dec_ref(v_pre_948_);
v_e_x3f_971_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_e_x3f_971_);
lean_dec_ref_known(v_a_961_, 1);
if (lean_obj_tag(v_e_x3f_971_) == 0)
{
lean_object* v___x_973_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_e_953_);
v___x_973_ = v___x_963_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_e_953_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v_val_975_; lean_object* v___x_977_; 
lean_dec_ref(v_e_953_);
v_val_975_ = lean_ctor_get(v_e_x3f_971_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v_e_x3f_971_, 1);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_val_975_);
v___x_977_ = v___x_963_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_val_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v_e_953_);
lean_dec_ref(v_post_949_);
lean_dec_ref(v_pre_948_);
v_a_980_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_960_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_960_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_988_, lean_object* v_post_989_, uint8_t v_usedLetOnly_990_, uint8_t v_skipConstInApp_991_, uint8_t v_skipInstances_992_, lean_object* v_fvars_993_, lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
if (lean_obj_tag(v_e_994_) == 6)
{
lean_object* v_binderName_1001_; lean_object* v_binderType_1002_; lean_object* v_body_1003_; uint8_t v_binderInfo_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_binderName_1001_ = lean_ctor_get(v_e_994_, 0);
lean_inc(v_binderName_1001_);
v_binderType_1002_ = lean_ctor_get(v_e_994_, 1);
lean_inc_ref(v_binderType_1002_);
v_body_1003_ = lean_ctor_get(v_e_994_, 2);
lean_inc_ref(v_body_1003_);
v_binderInfo_1004_ = lean_ctor_get_uint8(v_e_994_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_994_, 3);
v___x_1005_ = lean_expr_instantiate_rev(v_binderType_1002_, v_fvars_993_);
lean_dec_ref(v_binderType_1002_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1005_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_box(v_usedLetOnly_990_);
v___x_1009_ = lean_box(v_skipConstInApp_991_);
v___x_1010_ = lean_box(v_skipInstances_992_);
v___f_1011_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1011_, 0, v_fvars_993_);
lean_closure_set(v___f_1011_, 1, v_pre_988_);
lean_closure_set(v___f_1011_, 2, v_post_989_);
lean_closure_set(v___f_1011_, 3, v___x_1008_);
lean_closure_set(v___f_1011_, 4, v___x_1009_);
lean_closure_set(v___f_1011_, 5, v___x_1010_);
lean_closure_set(v___f_1011_, 6, v_body_1003_);
v___x_1012_ = 0;
v___x_1013_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1001_, v_binderInfo_1004_, v_a_1007_, v___f_1011_, v___x_1012_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1013_;
}
else
{
lean_dec_ref(v_body_1003_);
lean_dec(v_binderName_1001_);
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1006_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_expr_instantiate_rev(v_e_994_, v_fvars_993_);
lean_dec_ref(v_e_994_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1014_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; uint8_t v___x_1017_; uint8_t v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = 0;
v___x_1018_ = 1;
v___x_1019_ = 1;
v___x_1020_ = l_Lean_Meta_mkLambdaFVars(v_fvars_993_, v_a_1016_, v___x_1017_, v_usedLetOnly_990_, v___x_1017_, v___x_1018_, v___x_1019_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec_ref(v_fvars_993_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v_a_1021_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1022_;
}
else
{
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1020_;
}
}
else
{
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_1023_, lean_object* v_pre_1024_, lean_object* v_post_1025_, uint8_t v_usedLetOnly_1026_, uint8_t v_skipConstInApp_1027_, uint8_t v_skipInstances_1028_, lean_object* v_body_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_array_push(v_fvars_1023_, v_x_1030_);
v___x_1038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1024_, v_post_1025_, v_usedLetOnly_1026_, v_skipConstInApp_1027_, v_skipInstances_1028_, v___x_1037_, v_body_1029_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_1039_, lean_object* v_pre_1040_, lean_object* v_post_1041_, lean_object* v_usedLetOnly_1042_, lean_object* v_skipConstInApp_1043_, lean_object* v_skipInstances_1044_, lean_object* v_body_1045_, lean_object* v_x_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v_usedLetOnly_boxed_1053_; uint8_t v_skipConstInApp_boxed_1054_; uint8_t v_skipInstances_boxed_1055_; lean_object* v_res_1056_; 
v_usedLetOnly_boxed_1053_ = lean_unbox(v_usedLetOnly_1042_);
v_skipConstInApp_boxed_1054_ = lean_unbox(v_skipConstInApp_1043_);
v_skipInstances_boxed_1055_ = lean_unbox(v_skipInstances_1044_);
v_res_1056_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_1039_, v_pre_1040_, v_post_1041_, v_usedLetOnly_boxed_1053_, v_skipConstInApp_boxed_1054_, v_skipInstances_boxed_1055_, v_body_1045_, v_x_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_1057_, lean_object* v_post_1058_, uint8_t v_usedLetOnly_1059_, uint8_t v_skipConstInApp_1060_, uint8_t v_skipInstances_1061_, lean_object* v_fvars_1062_, lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
if (lean_obj_tag(v_e_1063_) == 8)
{
lean_object* v_declName_1070_; lean_object* v_type_1071_; lean_object* v_value_1072_; lean_object* v_body_1073_; uint8_t v_nondep_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_declName_1070_ = lean_ctor_get(v_e_1063_, 0);
lean_inc(v_declName_1070_);
v_type_1071_ = lean_ctor_get(v_e_1063_, 1);
lean_inc_ref(v_type_1071_);
v_value_1072_ = lean_ctor_get(v_e_1063_, 2);
lean_inc_ref(v_value_1072_);
v_body_1073_ = lean_ctor_get(v_e_1063_, 3);
lean_inc_ref(v_body_1073_);
v_nondep_1074_ = lean_ctor_get_uint8(v_e_1063_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1063_, 4);
v___x_1075_ = lean_expr_instantiate_rev(v_type_1071_, v_fvars_1062_);
lean_dec_ref(v_type_1071_);
lean_inc_ref(v_post_1058_);
lean_inc_ref(v_pre_1057_);
v___x_1076_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1057_, v_post_1058_, v_usedLetOnly_1059_, v_skipConstInApp_1060_, v_skipInstances_1061_, v___x_1075_, v_a_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = lean_expr_instantiate_rev(v_value_1072_, v_fvars_1062_);
lean_dec_ref(v_value_1072_);
lean_inc_ref(v_post_1058_);
lean_inc_ref(v_pre_1057_);
v___x_1079_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1057_, v_post_1058_, v_usedLetOnly_1059_, v_skipConstInApp_1060_, v_skipInstances_1061_, v___x_1078_, v_a_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___f_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_box(v_usedLetOnly_1059_);
v___x_1082_ = lean_box(v_skipConstInApp_1060_);
v___x_1083_ = lean_box(v_skipInstances_1061_);
v___f_1084_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1084_, 0, v_fvars_1062_);
lean_closure_set(v___f_1084_, 1, v_pre_1057_);
lean_closure_set(v___f_1084_, 2, v_post_1058_);
lean_closure_set(v___f_1084_, 3, v___x_1081_);
lean_closure_set(v___f_1084_, 4, v___x_1082_);
lean_closure_set(v___f_1084_, 5, v___x_1083_);
lean_closure_set(v___f_1084_, 6, v_body_1073_);
v___x_1085_ = 0;
v___x_1086_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_1070_, v_a_1077_, v_a_1080_, v___f_1084_, v_nondep_1074_, v___x_1085_, v_a_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1086_;
}
else
{
lean_dec(v_a_1077_);
lean_dec_ref(v_body_1073_);
lean_dec(v_declName_1070_);
lean_dec_ref(v_fvars_1062_);
lean_dec_ref(v_post_1058_);
lean_dec_ref(v_pre_1057_);
return v___x_1079_;
}
}
else
{
lean_dec_ref(v_body_1073_);
lean_dec_ref(v_value_1072_);
lean_dec(v_declName_1070_);
lean_dec_ref(v_fvars_1062_);
lean_dec_ref(v_post_1058_);
lean_dec_ref(v_pre_1057_);
return v___x_1076_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_expr_instantiate_rev(v_e_1063_, v_fvars_1062_);
lean_dec_ref(v_e_1063_);
lean_inc_ref(v_post_1058_);
lean_inc_ref(v_pre_1057_);
v___x_1088_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1057_, v_post_1058_, v_usedLetOnly_1059_, v_skipConstInApp_1060_, v_skipInstances_1061_, v___x_1087_, v_a_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; uint8_t v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = 0;
v___x_1091_ = 1;
v___x_1092_ = l_Lean_Meta_mkLetFVars(v_fvars_1062_, v_a_1089_, v_usedLetOnly_1059_, v___x_1090_, v___x_1091_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec_ref(v_fvars_1062_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1057_, v_post_1058_, v_usedLetOnly_1059_, v_skipConstInApp_1060_, v_skipInstances_1061_, v_a_1093_, v_a_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
return v___x_1094_;
}
else
{
lean_dec_ref(v_post_1058_);
lean_dec_ref(v_pre_1057_);
return v___x_1092_;
}
}
else
{
lean_dec_ref(v_fvars_1062_);
lean_dec_ref(v_post_1058_);
lean_dec_ref(v_pre_1057_);
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1095_, lean_object* v_post_1096_, uint8_t v_usedLetOnly_1097_, uint8_t v_skipConstInApp_1098_, uint8_t v_skipInstances_1099_, size_t v_sz_1100_, size_t v_i_1101_, lean_object* v_bs_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_usize_dec_lt(v_i_1101_, v_sz_1100_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_post_1096_);
lean_dec_ref(v_pre_1095_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_bs_1102_);
return v___x_1110_;
}
else
{
lean_object* v_v_1111_; lean_object* v___x_1112_; 
v_v_1111_ = lean_array_uget_borrowed(v_bs_1102_, v_i_1101_);
lean_inc(v_v_1111_);
lean_inc_ref(v_post_1096_);
lean_inc_ref(v_pre_1095_);
v___x_1112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1095_, v_post_1096_, v_usedLetOnly_1097_, v_skipConstInApp_1098_, v_skipInstances_1099_, v_v_1111_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1102_, v_i_1101_, v___x_1114_);
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1101_, v___x_1116_);
v___x_1118_ = lean_array_uset(v_bs_x27_1115_, v_i_1101_, v_a_1113_);
v_i_1101_ = v___x_1117_;
v_bs_1102_ = v___x_1118_;
goto _start;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_bs_1102_);
lean_dec_ref(v_post_1096_);
lean_dec_ref(v_pre_1095_);
v_a_1120_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1112_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1112_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1128_, lean_object* v_post_1129_, uint8_t v_usedLetOnly_1130_, uint8_t v_skipConstInApp_1131_, uint8_t v_skipInstances_1132_, lean_object* v___x_1133_, lean_object* v___y_1134_, lean_object* v_b_1135_, lean_object* v_a_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1128_, v_post_1129_, v_usedLetOnly_1130_, v_skipConstInApp_1131_, v_skipInstances_1132_, v___x_1133_, v___y_1134_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1152_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1147_ = lean_array_fset(v_b_1135_, v_a_1136_, v_a_1143_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_b_1135_);
v_a_1153_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1142_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1142_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1161_, lean_object* v_post_1162_, lean_object* v_usedLetOnly_1163_, lean_object* v_skipConstInApp_1164_, lean_object* v_skipInstances_1165_, lean_object* v___x_1166_, lean_object* v___y_1167_, lean_object* v_b_1168_, lean_object* v_a_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v_usedLetOnly_boxed_1175_; uint8_t v_skipConstInApp_boxed_1176_; uint8_t v_skipInstances_boxed_1177_; lean_object* v_res_1178_; 
v_usedLetOnly_boxed_1175_ = lean_unbox(v_usedLetOnly_1163_);
v_skipConstInApp_boxed_1176_ = lean_unbox(v_skipConstInApp_1164_);
v_skipInstances_boxed_1177_ = lean_unbox(v_skipInstances_1165_);
v_res_1178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1161_, v_post_1162_, v_usedLetOnly_boxed_1175_, v_skipConstInApp_boxed_1176_, v_skipInstances_boxed_1177_, v___x_1166_, v___y_1167_, v_b_1168_, v_a_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v_a_1169_);
lean_dec(v___y_1167_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1179_, lean_object* v___x_1180_, lean_object* v_pre_1181_, lean_object* v_post_1182_, uint8_t v_usedLetOnly_1183_, uint8_t v_skipConstInApp_1184_, uint8_t v_skipInstances_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___y_1195_; uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_lt(v_a_1186_, v_upperBound_1179_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; 
lean_dec(v_a_1186_);
lean_dec_ref(v_post_1182_);
lean_dec_ref(v_pre_1181_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_b_1187_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_array_fget_borrowed(v_b_1187_, v_a_1186_);
v___x_1221_ = lean_array_get_size(v___x_1180_);
v___x_1222_ = lean_nat_dec_lt(v_a_1186_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___f_1226_; 
lean_inc(v___x_1220_);
v___x_1223_ = lean_box(v_usedLetOnly_1183_);
v___x_1224_ = lean_box(v_skipConstInApp_1184_);
v___x_1225_ = lean_box(v_skipInstances_1185_);
lean_inc(v_a_1186_);
lean_inc(v___y_1188_);
lean_inc_ref(v_post_1182_);
lean_inc_ref(v_pre_1181_);
v___f_1226_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1226_, 0, v_pre_1181_);
lean_closure_set(v___f_1226_, 1, v_post_1182_);
lean_closure_set(v___f_1226_, 2, v___x_1223_);
lean_closure_set(v___f_1226_, 3, v___x_1224_);
lean_closure_set(v___f_1226_, 4, v___x_1225_);
lean_closure_set(v___f_1226_, 5, v___x_1220_);
lean_closure_set(v___f_1226_, 6, v___y_1188_);
lean_closure_set(v___f_1226_, 7, v_b_1187_);
lean_closure_set(v___f_1226_, 8, v_a_1186_);
v___y_1195_ = v___f_1226_;
goto v___jp_1194_;
}
else
{
lean_object* v___x_1227_; uint8_t v_isInstance_1228_; 
v___x_1227_ = lean_array_fget_borrowed(v___x_1180_, v_a_1186_);
v_isInstance_1228_ = lean_ctor_get_uint8(v___x_1227_, sizeof(void*)*1 + 4);
if (v_isInstance_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___f_1232_; 
lean_inc(v___x_1220_);
v___x_1229_ = lean_box(v_usedLetOnly_1183_);
v___x_1230_ = lean_box(v_skipConstInApp_1184_);
v___x_1231_ = lean_box(v_skipInstances_1185_);
lean_inc(v_a_1186_);
lean_inc(v___y_1188_);
lean_inc_ref(v_post_1182_);
lean_inc_ref(v_pre_1181_);
v___f_1232_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1232_, 0, v_pre_1181_);
lean_closure_set(v___f_1232_, 1, v_post_1182_);
lean_closure_set(v___f_1232_, 2, v___x_1229_);
lean_closure_set(v___f_1232_, 3, v___x_1230_);
lean_closure_set(v___f_1232_, 4, v___x_1231_);
lean_closure_set(v___f_1232_, 5, v___x_1220_);
lean_closure_set(v___f_1232_, 6, v___y_1188_);
lean_closure_set(v___f_1232_, 7, v_b_1187_);
lean_closure_set(v___f_1232_, 8, v_a_1186_);
v___y_1195_ = v___f_1232_;
goto v___jp_1194_;
}
else
{
lean_object* v___x_1233_; lean_object* v___f_1234_; 
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_b_1187_);
v___f_1234_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1234_, 0, v___x_1233_);
v___y_1195_ = v___f_1234_;
goto v___jp_1194_;
}
}
}
v___jp_1194_:
{
lean_object* v___x_1196_; 
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
v___x_1196_ = lean_apply_5(v___y_1195_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, lean_box(0));
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1209_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
if (lean_obj_tag(v_a_1197_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; 
lean_dec(v_a_1186_);
lean_dec_ref(v_post_1182_);
lean_dec_ref(v_pre_1181_);
v_a_1201_ = lean_ctor_get(v_a_1197_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v_a_1197_, 1);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v_a_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_del_object(v___x_1199_);
v_a_1205_ = lean_ctor_get(v_a_1197_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v_a_1197_, 1);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_a_1186_, v___x_1206_);
lean_dec(v_a_1186_);
v_a_1186_ = v___x_1207_;
v_b_1187_ = v_a_1205_;
goto _start;
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_a_1186_);
lean_dec_ref(v_post_1182_);
lean_dec_ref(v_pre_1181_);
v_a_1210_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1196_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1196_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1235_, lean_object* v_pre_1236_, lean_object* v_post_1237_, uint8_t v_usedLetOnly_1238_, uint8_t v_skipConstInApp_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_f_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; 
if (lean_obj_tag(v_x_1240_) == 5)
{
lean_object* v_fn_1298_; lean_object* v_arg_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_fn_1298_ = lean_ctor_get(v_x_1240_, 0);
lean_inc_ref(v_fn_1298_);
v_arg_1299_ = lean_ctor_get(v_x_1240_, 1);
lean_inc_ref(v_arg_1299_);
lean_dec_ref_known(v_x_1240_, 2);
v___x_1300_ = lean_array_set(v_x_1241_, v_x_1242_, v_arg_1299_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_sub(v_x_1242_, v___x_1301_);
lean_dec(v_x_1242_);
v_x_1240_ = v_fn_1298_;
v_x_1241_ = v___x_1300_;
v_x_1242_ = v___x_1302_;
goto _start;
}
else
{
lean_dec(v_x_1242_);
if (v_skipConstInApp_1239_ == 0)
{
goto v___jp_1295_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Lean_Expr_isConst(v_x_1240_);
if (v___x_1304_ == 0)
{
goto v___jp_1295_;
}
else
{
v_f_1250_ = v_x_1240_;
v___y_1251_ = v___y_1243_;
v___y_1252_ = v___y_1244_;
v___y_1253_ = v___y_1245_;
v___y_1254_ = v___y_1246_;
v___y_1255_ = v___y_1247_;
goto v___jp_1249_;
}
}
}
v___jp_1249_:
{
if (v_skipInstances_1235_ == 0)
{
size_t v_sz_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v_sz_1256_ = lean_array_size(v_x_1241_);
v___x_1257_ = ((size_t)0ULL);
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1236_);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1235_, v_sz_1256_, v___x_1257_, v_x_1241_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_mkAppN(v_f_1250_, v_a_1259_);
lean_dec(v_a_1259_);
v___x_1261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1235_, v___x_1260_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1261_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_f_1250_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
v_a_1262_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1258_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_array_get_size(v_x_1241_);
lean_inc_ref(v_f_1250_);
v___x_1271_ = l_Lean_Meta_getFunInfoNArgs(v_f_1250_, v___x_1270_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_paramInfo_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_paramInfo_1273_ = lean_ctor_get(v_a_1272_, 0);
lean_inc_ref(v_paramInfo_1273_);
lean_dec(v_a_1272_);
v___x_1274_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1236_);
v___x_1275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1270_, v_paramInfo_1273_, v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1235_, v___x_1274_, v_x_1241_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec_ref(v_paramInfo_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l_Lean_mkAppN(v_f_1250_, v_a_1276_);
lean_dec(v_a_1276_);
v___x_1278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1235_, v___x_1277_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1278_;
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v_f_1250_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
v_a_1279_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1275_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1275_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_f_1250_);
lean_dec_ref(v_x_1241_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
v_a_1287_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1271_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1271_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
v___jp_1295_:
{
lean_object* v___x_1296_; 
lean_inc_ref(v_post_1237_);
lean_inc_ref(v_pre_1236_);
v___x_1296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1236_, v_post_1237_, v_usedLetOnly_1238_, v_skipConstInApp_1239_, v_skipInstances_1235_, v_x_1240_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v_f_1250_ = v_a_1297_;
v___y_1251_ = v___y_1243_;
v___y_1252_ = v___y_1244_;
v___y_1253_ = v___y_1245_;
v___y_1254_ = v___y_1246_;
v___y_1255_ = v___y_1247_;
goto v___jp_1249_;
}
else
{
lean_dec_ref(v_x_1241_);
lean_dec_ref(v_post_1237_);
lean_dec_ref(v_pre_1236_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1305_, lean_object* v_pre_1306_, lean_object* v_e_1307_, lean_object* v_post_1308_, uint8_t v_usedLetOnly_1309_, uint8_t v_skipConstInApp_1310_, uint8_t v_skipInstances_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Core_checkSystem(v___x_1305_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref_known(v___x_1318_, 1);
lean_inc_ref(v_pre_1306_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
lean_inc_ref(v_e_1307_);
v___x_1319_ = lean_apply_6(v_pre_1306_, v_e_1307_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, lean_box(0));
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1368_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1368_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1368_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___y_1325_; 
switch(lean_obj_tag(v_a_1320_))
{
case 0:
{
lean_object* v_e_1360_; lean_object* v___x_1362_; 
lean_dec_ref(v_post_1308_);
lean_dec_ref(v_e_1307_);
lean_dec_ref(v_pre_1306_);
v_e_1360_ = lean_ctor_get(v_a_1320_, 0);
lean_inc_ref(v_e_1360_);
lean_dec_ref_known(v_a_1320_, 1);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_e_1360_);
v___x_1362_ = v___x_1322_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_e_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
case 1:
{
lean_object* v_e_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1322_);
lean_dec_ref(v_e_1307_);
v_e_1364_ = lean_ctor_get(v_a_1320_, 0);
lean_inc_ref(v_e_1364_);
lean_dec_ref_known(v_a_1320_, 1);
v___x_1365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v_e_1364_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1365_;
}
default: 
{
lean_object* v_e_x3f_1366_; 
lean_del_object(v___x_1322_);
v_e_x3f_1366_ = lean_ctor_get(v_a_1320_, 0);
lean_inc(v_e_x3f_1366_);
lean_dec_ref_known(v_a_1320_, 1);
if (lean_obj_tag(v_e_x3f_1366_) == 0)
{
v___y_1325_ = v_e_1307_;
goto v___jp_1324_;
}
else
{
lean_object* v_val_1367_; 
lean_dec_ref(v_e_1307_);
v_val_1367_ = lean_ctor_get(v_e_x3f_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v_e_x3f_1366_, 1);
v___y_1325_ = v_val_1367_;
goto v___jp_1324_;
}
}
}
v___jp_1324_:
{
switch(lean_obj_tag(v___y_1325_))
{
case 7:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___x_1326_, v___y_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1327_;
}
case 6:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___x_1328_, v___y_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1329_;
}
case 8:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1331_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___x_1330_, v___y_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1331_;
}
case 5:
{
lean_object* v_dummy_1332_; lean_object* v_nargs_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_dummy_1332_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1333_ = l_Lean_Expr_getAppNumArgs(v___y_1325_);
lean_inc(v_nargs_1333_);
v___x_1334_ = lean_mk_array(v_nargs_1333_, v_dummy_1332_);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_sub(v_nargs_1333_, v___x_1335_);
lean_dec(v_nargs_1333_);
v___x_1337_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1311_, v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v___y_1325_, v___x_1334_, v___x_1336_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1337_;
}
case 10:
{
lean_object* v_data_1338_; lean_object* v_expr_1339_; lean_object* v___x_1340_; 
v_data_1338_ = lean_ctor_get(v___y_1325_, 0);
v_expr_1339_ = lean_ctor_get(v___y_1325_, 1);
lean_inc_ref(v_expr_1339_);
lean_inc_ref(v_post_1308_);
lean_inc_ref(v_pre_1306_);
v___x_1340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v_expr_1339_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; size_t v___x_1342_; size_t v___x_1343_; uint8_t v___x_1344_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = lean_ptr_addr(v_expr_1339_);
v___x_1343_ = lean_ptr_addr(v_a_1341_);
v___x_1344_ = lean_usize_dec_eq(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_inc(v_data_1338_);
lean_dec_ref_known(v___y_1325_, 2);
v___x_1345_ = l_Lean_Expr_mdata___override(v_data_1338_, v_a_1341_);
v___x_1346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___x_1345_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v_a_1341_);
v___x_1347_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___y_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1347_;
}
}
else
{
lean_dec_ref_known(v___y_1325_, 2);
lean_dec_ref(v_post_1308_);
lean_dec_ref(v_pre_1306_);
return v___x_1340_;
}
}
case 11:
{
lean_object* v_typeName_1348_; lean_object* v_idx_1349_; lean_object* v_struct_1350_; lean_object* v___x_1351_; 
v_typeName_1348_ = lean_ctor_get(v___y_1325_, 0);
v_idx_1349_ = lean_ctor_get(v___y_1325_, 1);
v_struct_1350_ = lean_ctor_get(v___y_1325_, 2);
lean_inc_ref(v_struct_1350_);
lean_inc_ref(v_post_1308_);
lean_inc_ref(v_pre_1306_);
v___x_1351_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v_struct_1350_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; size_t v___x_1353_; size_t v___x_1354_; uint8_t v___x_1355_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_ptr_addr(v_struct_1350_);
v___x_1354_ = lean_ptr_addr(v_a_1352_);
v___x_1355_ = lean_usize_dec_eq(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_inc(v_idx_1349_);
lean_inc(v_typeName_1348_);
lean_dec_ref_known(v___y_1325_, 3);
v___x_1356_ = l_Lean_Expr_proj___override(v_typeName_1348_, v_idx_1349_, v_a_1352_);
v___x_1357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___x_1356_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; 
lean_dec(v_a_1352_);
v___x_1358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___y_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1358_;
}
}
else
{
lean_dec_ref_known(v___y_1325_, 3);
lean_dec_ref(v_post_1308_);
lean_dec_ref(v_pre_1306_);
return v___x_1351_;
}
}
default: 
{
lean_object* v___x_1359_; 
v___x_1359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1306_, v_post_1308_, v_usedLetOnly_1309_, v_skipConstInApp_1310_, v_skipInstances_1311_, v___y_1325_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1359_;
}
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_post_1308_);
lean_dec_ref(v_e_1307_);
lean_dec_ref(v_pre_1306_);
v_a_1369_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1319_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1319_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_post_1308_);
lean_dec_ref(v_e_1307_);
lean_dec_ref(v_pre_1306_);
v_a_1377_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1318_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1318_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1385_, lean_object* v_pre_1386_, lean_object* v_e_1387_, lean_object* v_post_1388_, lean_object* v_usedLetOnly_1389_, lean_object* v_skipConstInApp_1390_, lean_object* v_skipInstances_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_usedLetOnly_boxed_1398_; uint8_t v_skipConstInApp_boxed_1399_; uint8_t v_skipInstances_boxed_1400_; lean_object* v_res_1401_; 
v_usedLetOnly_boxed_1398_ = lean_unbox(v_usedLetOnly_1389_);
v_skipConstInApp_boxed_1399_ = lean_unbox(v_skipConstInApp_1390_);
v_skipInstances_boxed_1400_ = lean_unbox(v_skipInstances_1391_);
v_res_1401_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1385_, v_pre_1386_, v_e_1387_, v_post_1388_, v_usedLetOnly_boxed_1398_, v_skipConstInApp_boxed_1399_, v_skipInstances_boxed_1400_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1402_, lean_object* v_post_1403_, uint8_t v_usedLetOnly_1404_, uint8_t v_skipConstInApp_1405_, uint8_t v_skipInstances_1406_, lean_object* v_e_1407_, lean_object* v_a_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_inc(v_a_1408_);
v___x_1414_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1414_, 0, lean_box(0));
lean_closure_set(v___x_1414_, 1, lean_box(0));
lean_closure_set(v___x_1414_, 2, v_a_1408_);
v___x_1415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1414_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1450_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1450_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1450_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1416_, v_e_1407_);
lean_dec(v_a_1416_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; 
lean_del_object(v___x_1418_);
v___x_1421_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1422_ = lean_box(v_usedLetOnly_1404_);
v___x_1423_ = lean_box(v_skipConstInApp_1405_);
v___x_1424_ = lean_box(v_skipInstances_1406_);
lean_inc_ref(v_e_1407_);
v___f_1425_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1425_, 0, v___x_1421_);
lean_closure_set(v___f_1425_, 1, v_pre_1402_);
lean_closure_set(v___f_1425_, 2, v_e_1407_);
lean_closure_set(v___f_1425_, 3, v_post_1403_);
lean_closure_set(v___f_1425_, 4, v___x_1422_);
lean_closure_set(v___f_1425_, 5, v___x_1423_);
lean_closure_set(v___f_1425_, 6, v___x_1424_);
v___x_1426_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1425_, v_a_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc_n(v_a_1427_, 2);
lean_dec_ref_known(v___x_1426_, 1);
lean_inc(v_a_1408_);
v___f_1428_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1428_, 0, v_a_1408_);
lean_closure_set(v___f_1428_, 1, v_e_1407_);
lean_closure_set(v___f_1428_, 2, v_a_1427_);
v___x_1429_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1428_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v___x_1429_, 0);
lean_dec(v_unused_1437_);
v___x_1431_ = v___x_1429_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v___x_1429_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v_a_1427_);
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1427_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1427_);
v_a_1438_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1429_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1429_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_dec_ref(v_e_1407_);
return v___x_1426_;
}
}
else
{
lean_object* v_val_1446_; lean_object* v___x_1448_; 
lean_dec_ref(v_e_1407_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
v_val_1446_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1446_);
lean_dec_ref_known(v___x_1420_, 1);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_val_1446_);
v___x_1448_ = v___x_1418_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_e_1407_);
lean_dec_ref(v_post_1403_);
lean_dec_ref(v_pre_1402_);
v_a_1451_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1415_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1415_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1459_, lean_object* v_pre_1460_, lean_object* v_post_1461_, lean_object* v_usedLetOnly_1462_, lean_object* v_skipConstInApp_1463_, lean_object* v_skipInstances_1464_, lean_object* v_body_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v_usedLetOnly_boxed_1473_; uint8_t v_skipConstInApp_boxed_1474_; uint8_t v_skipInstances_boxed_1475_; lean_object* v_res_1476_; 
v_usedLetOnly_boxed_1473_ = lean_unbox(v_usedLetOnly_1462_);
v_skipConstInApp_boxed_1474_ = lean_unbox(v_skipConstInApp_1463_);
v_skipInstances_boxed_1475_ = lean_unbox(v_skipInstances_1464_);
v_res_1476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1459_, v_pre_1460_, v_post_1461_, v_usedLetOnly_boxed_1473_, v_skipConstInApp_boxed_1474_, v_skipInstances_boxed_1475_, v_body_1465_, v_x_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1477_, lean_object* v_post_1478_, uint8_t v_usedLetOnly_1479_, uint8_t v_skipConstInApp_1480_, uint8_t v_skipInstances_1481_, lean_object* v_fvars_1482_, lean_object* v_e_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
if (lean_obj_tag(v_e_1483_) == 7)
{
lean_object* v_binderName_1490_; lean_object* v_binderType_1491_; lean_object* v_body_1492_; uint8_t v_binderInfo_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_binderName_1490_ = lean_ctor_get(v_e_1483_, 0);
lean_inc(v_binderName_1490_);
v_binderType_1491_ = lean_ctor_get(v_e_1483_, 1);
lean_inc_ref(v_binderType_1491_);
v_body_1492_ = lean_ctor_get(v_e_1483_, 2);
lean_inc_ref(v_body_1492_);
v_binderInfo_1493_ = lean_ctor_get_uint8(v_e_1483_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1483_, 3);
v___x_1494_ = lean_expr_instantiate_rev(v_binderType_1491_, v_fvars_1482_);
lean_dec_ref(v_binderType_1491_);
lean_inc_ref(v_post_1478_);
lean_inc_ref(v_pre_1477_);
v___x_1495_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1477_, v_post_1478_, v_usedLetOnly_1479_, v_skipConstInApp_1480_, v_skipInstances_1481_, v___x_1494_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = lean_box(v_usedLetOnly_1479_);
v___x_1498_ = lean_box(v_skipConstInApp_1480_);
v___x_1499_ = lean_box(v_skipInstances_1481_);
v___f_1500_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1500_, 0, v_fvars_1482_);
lean_closure_set(v___f_1500_, 1, v_pre_1477_);
lean_closure_set(v___f_1500_, 2, v_post_1478_);
lean_closure_set(v___f_1500_, 3, v___x_1497_);
lean_closure_set(v___f_1500_, 4, v___x_1498_);
lean_closure_set(v___f_1500_, 5, v___x_1499_);
lean_closure_set(v___f_1500_, 6, v_body_1492_);
v___x_1501_ = 0;
v___x_1502_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1490_, v_binderInfo_1493_, v_a_1496_, v___f_1500_, v___x_1501_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1502_;
}
else
{
lean_dec_ref(v_body_1492_);
lean_dec(v_binderName_1490_);
lean_dec_ref(v_fvars_1482_);
lean_dec_ref(v_post_1478_);
lean_dec_ref(v_pre_1477_);
return v___x_1495_;
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_expr_instantiate_rev(v_e_1483_, v_fvars_1482_);
lean_dec_ref(v_e_1483_);
lean_inc_ref(v_post_1478_);
lean_inc_ref(v_pre_1477_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1477_, v_post_1478_, v_usedLetOnly_1479_, v_skipConstInApp_1480_, v_skipInstances_1481_, v___x_1503_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; uint8_t v___x_1506_; uint8_t v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = 0;
v___x_1507_ = 1;
v___x_1508_ = 1;
v___x_1509_ = l_Lean_Meta_mkForallFVars(v_fvars_1482_, v_a_1505_, v___x_1506_, v_usedLetOnly_1479_, v___x_1507_, v___x_1508_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec_ref(v_fvars_1482_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1477_, v_post_1478_, v_usedLetOnly_1479_, v_skipConstInApp_1480_, v_skipInstances_1481_, v_a_1510_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1511_;
}
else
{
lean_dec_ref(v_post_1478_);
lean_dec_ref(v_pre_1477_);
return v___x_1509_;
}
}
else
{
lean_dec_ref(v_fvars_1482_);
lean_dec_ref(v_post_1478_);
lean_dec_ref(v_pre_1477_);
return v___x_1504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1512_, lean_object* v_pre_1513_, lean_object* v_post_1514_, uint8_t v_usedLetOnly_1515_, uint8_t v_skipConstInApp_1516_, uint8_t v_skipInstances_1517_, lean_object* v_body_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_array_push(v_fvars_1512_, v_x_1519_);
v___x_1527_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1513_, v_post_1514_, v_usedLetOnly_1515_, v_skipConstInApp_1516_, v_skipInstances_1517_, v___x_1526_, v_body_1518_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1528_, lean_object* v_post_1529_, lean_object* v_usedLetOnly_1530_, lean_object* v_skipConstInApp_1531_, lean_object* v_skipInstances_1532_, lean_object* v_e_1533_, lean_object* v_a_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v_usedLetOnly_boxed_1540_; uint8_t v_skipConstInApp_boxed_1541_; uint8_t v_skipInstances_boxed_1542_; lean_object* v_res_1543_; 
v_usedLetOnly_boxed_1540_ = lean_unbox(v_usedLetOnly_1530_);
v_skipConstInApp_boxed_1541_ = lean_unbox(v_skipConstInApp_1531_);
v_skipInstances_boxed_1542_ = lean_unbox(v_skipInstances_1532_);
v_res_1543_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1528_, v_post_1529_, v_usedLetOnly_boxed_1540_, v_skipConstInApp_boxed_1541_, v_skipInstances_boxed_1542_, v_e_1533_, v_a_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_a_1534_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1544_, lean_object* v_post_1545_, lean_object* v_usedLetOnly_1546_, lean_object* v_skipConstInApp_1547_, lean_object* v_skipInstances_1548_, lean_object* v_sz_1549_, lean_object* v_i_1550_, lean_object* v_bs_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_usedLetOnly_boxed_1558_; uint8_t v_skipConstInApp_boxed_1559_; uint8_t v_skipInstances_boxed_1560_; size_t v_sz_boxed_1561_; size_t v_i_boxed_1562_; lean_object* v_res_1563_; 
v_usedLetOnly_boxed_1558_ = lean_unbox(v_usedLetOnly_1546_);
v_skipConstInApp_boxed_1559_ = lean_unbox(v_skipConstInApp_1547_);
v_skipInstances_boxed_1560_ = lean_unbox(v_skipInstances_1548_);
v_sz_boxed_1561_ = lean_unbox_usize(v_sz_1549_);
lean_dec(v_sz_1549_);
v_i_boxed_1562_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1544_, v_post_1545_, v_usedLetOnly_boxed_1558_, v_skipConstInApp_boxed_1559_, v_skipInstances_boxed_1560_, v_sz_boxed_1561_, v_i_boxed_1562_, v_bs_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1564_, lean_object* v_post_1565_, lean_object* v_usedLetOnly_1566_, lean_object* v_skipConstInApp_1567_, lean_object* v_skipInstances_1568_, lean_object* v_e_1569_, lean_object* v_a_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v_usedLetOnly_boxed_1576_; uint8_t v_skipConstInApp_boxed_1577_; uint8_t v_skipInstances_boxed_1578_; lean_object* v_res_1579_; 
v_usedLetOnly_boxed_1576_ = lean_unbox(v_usedLetOnly_1566_);
v_skipConstInApp_boxed_1577_ = lean_unbox(v_skipConstInApp_1567_);
v_skipInstances_boxed_1578_ = lean_unbox(v_skipInstances_1568_);
v_res_1579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1564_, v_post_1565_, v_usedLetOnly_boxed_1576_, v_skipConstInApp_boxed_1577_, v_skipInstances_boxed_1578_, v_e_1569_, v_a_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v_a_1570_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1580_, lean_object* v_post_1581_, lean_object* v_usedLetOnly_1582_, lean_object* v_skipConstInApp_1583_, lean_object* v_skipInstances_1584_, lean_object* v_fvars_1585_, lean_object* v_e_1586_, lean_object* v_a_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v_usedLetOnly_boxed_1593_; uint8_t v_skipConstInApp_boxed_1594_; uint8_t v_skipInstances_boxed_1595_; lean_object* v_res_1596_; 
v_usedLetOnly_boxed_1593_ = lean_unbox(v_usedLetOnly_1582_);
v_skipConstInApp_boxed_1594_ = lean_unbox(v_skipConstInApp_1583_);
v_skipInstances_boxed_1595_ = lean_unbox(v_skipInstances_1584_);
v_res_1596_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1580_, v_post_1581_, v_usedLetOnly_boxed_1593_, v_skipConstInApp_boxed_1594_, v_skipInstances_boxed_1595_, v_fvars_1585_, v_e_1586_, v_a_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v_a_1587_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1597_, lean_object* v_post_1598_, lean_object* v_usedLetOnly_1599_, lean_object* v_skipConstInApp_1600_, lean_object* v_skipInstances_1601_, lean_object* v_fvars_1602_, lean_object* v_e_1603_, lean_object* v_a_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v_usedLetOnly_boxed_1610_; uint8_t v_skipConstInApp_boxed_1611_; uint8_t v_skipInstances_boxed_1612_; lean_object* v_res_1613_; 
v_usedLetOnly_boxed_1610_ = lean_unbox(v_usedLetOnly_1599_);
v_skipConstInApp_boxed_1611_ = lean_unbox(v_skipConstInApp_1600_);
v_skipInstances_boxed_1612_ = lean_unbox(v_skipInstances_1601_);
v_res_1613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1597_, v_post_1598_, v_usedLetOnly_boxed_1610_, v_skipConstInApp_boxed_1611_, v_skipInstances_boxed_1612_, v_fvars_1602_, v_e_1603_, v_a_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v_a_1604_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1614_, lean_object* v_post_1615_, lean_object* v_usedLetOnly_1616_, lean_object* v_skipConstInApp_1617_, lean_object* v_skipInstances_1618_, lean_object* v_fvars_1619_, lean_object* v_e_1620_, lean_object* v_a_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_usedLetOnly_boxed_1627_; uint8_t v_skipConstInApp_boxed_1628_; uint8_t v_skipInstances_boxed_1629_; lean_object* v_res_1630_; 
v_usedLetOnly_boxed_1627_ = lean_unbox(v_usedLetOnly_1616_);
v_skipConstInApp_boxed_1628_ = lean_unbox(v_skipConstInApp_1617_);
v_skipInstances_boxed_1629_ = lean_unbox(v_skipInstances_1618_);
v_res_1630_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1614_, v_post_1615_, v_usedLetOnly_boxed_1627_, v_skipConstInApp_boxed_1628_, v_skipInstances_boxed_1629_, v_fvars_1619_, v_e_1620_, v_a_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v_a_1621_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1631_, lean_object* v___x_1632_, lean_object* v_pre_1633_, lean_object* v_post_1634_, lean_object* v_usedLetOnly_1635_, lean_object* v_skipConstInApp_1636_, lean_object* v_skipInstances_1637_, lean_object* v_a_1638_, lean_object* v_b_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_usedLetOnly_boxed_1646_; uint8_t v_skipConstInApp_boxed_1647_; uint8_t v_skipInstances_boxed_1648_; lean_object* v_res_1649_; 
v_usedLetOnly_boxed_1646_ = lean_unbox(v_usedLetOnly_1635_);
v_skipConstInApp_boxed_1647_ = lean_unbox(v_skipConstInApp_1636_);
v_skipInstances_boxed_1648_ = lean_unbox(v_skipInstances_1637_);
v_res_1649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1631_, v___x_1632_, v_pre_1633_, v_post_1634_, v_usedLetOnly_boxed_1646_, v_skipConstInApp_boxed_1647_, v_skipInstances_boxed_1648_, v_a_1638_, v_b_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___x_1632_);
lean_dec(v_upperBound_1631_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1650_, lean_object* v_pre_1651_, lean_object* v_post_1652_, lean_object* v_usedLetOnly_1653_, lean_object* v_skipConstInApp_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_skipInstances_boxed_1664_; uint8_t v_usedLetOnly_boxed_1665_; uint8_t v_skipConstInApp_boxed_1666_; lean_object* v_res_1667_; 
v_skipInstances_boxed_1664_ = lean_unbox(v_skipInstances_1650_);
v_usedLetOnly_boxed_1665_ = lean_unbox(v_usedLetOnly_1653_);
v_skipConstInApp_boxed_1666_ = lean_unbox(v_skipConstInApp_1654_);
v_res_1667_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1664_, v_pre_1651_, v_post_1652_, v_usedLetOnly_boxed_1665_, v_skipConstInApp_boxed_1666_, v_x_1655_, v_x_1656_, v_x_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
return v_res_1667_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v_cellCount_1668_; lean_object* v___x_1669_; 
v_cellCount_1668_ = lean_unsigned_to_nat(16u);
v___x_1669_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v_cellCount_1670_; lean_object* v___x_1671_; 
v_cellCount_1670_ = lean_unsigned_to_nat(16u);
v___x_1671_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1672_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1673_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___x_1673_);
lean_ctor_set(v___x_1675_, 2, v___x_1672_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1677_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1677_, 0, lean_box(0));
lean_closure_set(v___x_1677_, 1, lean_box(0));
lean_closure_set(v___x_1677_, 2, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1678_, lean_object* v_pre_1679_, lean_object* v_post_1680_, uint8_t v_usedLetOnly_1681_, uint8_t v_skipConstInApp_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1688_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__3);
v___x_1689_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1688_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = 0;
v___x_1692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1679_, v_post_1680_, v_usedLetOnly_1681_, v_skipConstInApp_1682_, v___x_1691_, v_input_1678_, v_a_1690_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1694_, 0, lean_box(0));
lean_closure_set(v___x_1694_, 1, lean_box(0));
lean_closure_set(v___x_1694_, 2, v_a_1690_);
v___x_1695_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1694_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v___x_1695_, 0);
lean_dec(v_unused_1703_);
v___x_1697_ = v___x_1695_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_dec(v___x_1695_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v_a_1693_);
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1693_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_dec(v_a_1690_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1704_, lean_object* v_pre_1705_, lean_object* v_post_1706_, lean_object* v_usedLetOnly_1707_, lean_object* v_skipConstInApp_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v_usedLetOnly_boxed_1714_; uint8_t v_skipConstInApp_boxed_1715_; lean_object* v_res_1716_; 
v_usedLetOnly_boxed_1714_ = lean_unbox(v_usedLetOnly_1707_);
v_skipConstInApp_boxed_1715_ = lean_unbox(v_skipConstInApp_1708_);
v_res_1716_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1704_, v_pre_1705_, v_post_1706_, v_usedLetOnly_boxed_1714_, v_skipConstInApp_boxed_1715_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1716_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__2(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__1));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__4(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__3));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1724_, lean_object* v_argsPacker_1725_, lean_object* v_funNames_1726_, lean_object* v_newF_1727_, lean_object* v_e_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
lean_inc(v_a_1732_);
lean_inc_ref(v_a_1731_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc_ref(v_newF_1727_);
v___x_1734_ = lean_infer_type(v_newF_1727_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___f_1736_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; uint8_t v___x_1747_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___f_1736_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1747_ = l_Lean_Expr_isForall(v_a_1735_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v_e_1728_);
lean_dec_ref(v_funNames_1726_);
lean_dec_ref(v_argsPacker_1725_);
lean_dec_ref(v_fixedParamPerms_1724_);
v___x_1748_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__2, &l_Lean_Elab_WF_packCalls___closed__2_once, _init_l_Lean_Elab_WF_packCalls___closed__2);
v___x_1749_ = l_Lean_MessageData_ofExpr(v_newF_1727_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__4, &l_Lean_Elab_WF_packCalls___closed__4_once, _init_l_Lean_Elab_WF_packCalls___closed__4);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = l_Lean_MessageData_ofExpr(v_a_1735_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1754_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
v___y_1738_ = v_a_1729_;
v___y_1739_ = v_a_1730_;
v___y_1740_ = v_a_1731_;
v___y_1741_ = v_a_1732_;
goto v___jp_1737_;
}
v___jp_1737_:
{
lean_object* v___x_1742_; lean_object* v___f_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1742_ = l_Lean_Expr_bindingDomain_x21(v_a_1735_);
lean_dec(v_a_1735_);
v___f_1743_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1743_, 0, v_funNames_1726_);
lean_closure_set(v___f_1743_, 1, v_fixedParamPerms_1724_);
lean_closure_set(v___f_1743_, 2, v_argsPacker_1725_);
lean_closure_set(v___f_1743_, 3, v___x_1742_);
lean_closure_set(v___f_1743_, 4, v_newF_1727_);
v___x_1744_ = 0;
v___x_1745_ = 1;
v___x_1746_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1728_, v___f_1736_, v___f_1743_, v___x_1744_, v___x_1745_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
return v___x_1746_;
}
}
else
{
lean_dec_ref(v_e_1728_);
lean_dec_ref(v_newF_1727_);
lean_dec_ref(v_funNames_1726_);
lean_dec_ref(v_argsPacker_1725_);
lean_dec_ref(v_fixedParamPerms_1724_);
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1764_, lean_object* v_argsPacker_1765_, lean_object* v_funNames_1766_, lean_object* v_newF_1767_, lean_object* v_e_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1764_, v_argsPacker_1765_, v_funNames_1766_, v_newF_1767_, v_e_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1775_, lean_object* v___x_1776_, lean_object* v_pre_1777_, lean_object* v_post_1778_, uint8_t v_usedLetOnly_1779_, uint8_t v_skipConstInApp_1780_, uint8_t v_skipInstances_1781_, lean_object* v___x_1782_, lean_object* v_inst_1783_, lean_object* v_R_1784_, lean_object* v_a_1785_, lean_object* v_b_1786_, lean_object* v_c_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1775_, v___x_1776_, v_pre_1777_, v_post_1778_, v_usedLetOnly_1779_, v_skipConstInApp_1780_, v_skipInstances_1781_, v_a_1785_, v_b_1786_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1795_ = _args[0];
lean_object* v___x_1796_ = _args[1];
lean_object* v_pre_1797_ = _args[2];
lean_object* v_post_1798_ = _args[3];
lean_object* v_usedLetOnly_1799_ = _args[4];
lean_object* v_skipConstInApp_1800_ = _args[5];
lean_object* v_skipInstances_1801_ = _args[6];
lean_object* v___x_1802_ = _args[7];
lean_object* v_inst_1803_ = _args[8];
lean_object* v_R_1804_ = _args[9];
lean_object* v_a_1805_ = _args[10];
lean_object* v_b_1806_ = _args[11];
lean_object* v_c_1807_ = _args[12];
lean_object* v___y_1808_ = _args[13];
lean_object* v___y_1809_ = _args[14];
lean_object* v___y_1810_ = _args[15];
lean_object* v___y_1811_ = _args[16];
lean_object* v___y_1812_ = _args[17];
lean_object* v___y_1813_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1814_; uint8_t v_skipConstInApp_boxed_1815_; uint8_t v_skipInstances_boxed_1816_; lean_object* v_res_1817_; 
v_usedLetOnly_boxed_1814_ = lean_unbox(v_usedLetOnly_1799_);
v_skipConstInApp_boxed_1815_ = lean_unbox(v_skipConstInApp_1800_);
v_skipInstances_boxed_1816_ = lean_unbox(v_skipInstances_1801_);
v_res_1817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1795_, v___x_1796_, v_pre_1797_, v_post_1798_, v_usedLetOnly_boxed_1814_, v_skipConstInApp_boxed_1815_, v_skipInstances_boxed_1816_, v___x_1802_, v_inst_1803_, v_R_1804_, v_a_1805_, v_b_1806_, v_c_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec(v___x_1802_);
lean_dec_ref(v___x_1796_);
lean_dec(v_upperBound_1795_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1818_, lean_object* v_m_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1819_, v_a_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1822_, lean_object* v_m_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1822_, v_m_1823_, v_a_1824_);
lean_dec_ref(v_a_1824_);
lean_dec_ref(v_m_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1826_, lean_object* v_name_1827_, uint8_t v_bi_1828_, lean_object* v_type_1829_, lean_object* v_k_1830_, uint8_t v_kind_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1827_, v_bi_1828_, v_type_1829_, v_k_1830_, v_kind_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1839_, lean_object* v_name_1840_, lean_object* v_bi_1841_, lean_object* v_type_1842_, lean_object* v_k_1843_, lean_object* v_kind_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
uint8_t v_bi_boxed_1851_; uint8_t v_kind_boxed_1852_; lean_object* v_res_1853_; 
v_bi_boxed_1851_ = lean_unbox(v_bi_1841_);
v_kind_boxed_1852_ = lean_unbox(v_kind_1844_);
v_res_1853_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1839_, v_name_1840_, v_bi_boxed_1851_, v_type_1842_, v_k_1843_, v_kind_boxed_1852_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1854_, lean_object* v_name_1855_, lean_object* v_type_1856_, lean_object* v_val_1857_, lean_object* v_k_1858_, uint8_t v_nondep_1859_, uint8_t v_kind_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1855_, v_type_1856_, v_val_1857_, v_k_1858_, v_nondep_1859_, v_kind_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_name_1869_, lean_object* v_type_1870_, lean_object* v_val_1871_, lean_object* v_k_1872_, lean_object* v_nondep_1873_, lean_object* v_kind_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v_nondep_boxed_1881_; uint8_t v_kind_boxed_1882_; lean_object* v_res_1883_; 
v_nondep_boxed_1881_ = lean_unbox(v_nondep_1873_);
v_kind_boxed_1882_ = lean_unbox(v_kind_1874_);
v_res_1883_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1868_, v_name_1869_, v_type_1870_, v_val_1871_, v_k_1872_, v_nondep_boxed_1881_, v_kind_boxed_1882_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1884_, lean_object* v_ref_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1885_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_ref_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1892_, v_ref_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1900_, lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_x_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1909_, v_x_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1918_, lean_object* v_m_1919_, lean_object* v_query_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1919_, v_query_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___boxed(lean_object* v_00_u03b2_1922_, lean_object* v_m_1923_, lean_object* v_query_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(v_00_u03b2_1922_, v_m_1923_, v_query_1924_);
lean_dec_ref(v_query_1924_);
lean_dec_ref(v_m_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16(lean_object* v_00_u03b2_1926_, lean_object* v_m_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___redArg(v_m_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16___boxed(lean_object* v_00_u03b2_1929_, lean_object* v_m_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16(v_00_u03b2_1929_, v_m_1930_);
lean_dec_ref(v_m_1930_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1932_, lean_object* v_m_1933_, lean_object* v_query_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_m_1933_, v_query_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1936_, lean_object* v_m_1937_, lean_object* v_query_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1936_, v_m_1937_, v_query_1938_);
lean_dec_ref(v_query_1938_);
lean_dec_ref(v_m_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1940_, lean_object* v_m_1941_, lean_object* v_query_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_m_1941_, v_query_1942_, v_x_1943_, v_x_1944_, v_x_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1948_, lean_object* v_m_1949_, lean_object* v_query_1950_, lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v_x_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1948_, v_m_1949_, v_query_1950_, v_x_1951_, v_x_1952_, v_x_1953_, v_x_1954_);
lean_dec_ref(v_query_1950_);
lean_dec_ref(v_m_1949_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22(lean_object* v_00_u03b2_1956_, lean_object* v_init_1957_, lean_object* v_b_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___redArg(v_init_1957_, v_b_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22___boxed(lean_object* v_00_u03b2_1960_, lean_object* v_init_1961_, lean_object* v_b_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22(v_00_u03b2_1960_, v_init_1961_, v_b_1962_);
lean_dec_ref(v_b_1962_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23(lean_object* v_00_u03b2_1964_, lean_object* v_b_1965_, lean_object* v_acc_1966_, lean_object* v_i_1967_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___redArg(v_b_1965_, v_acc_1966_, v_i_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23___boxed(lean_object* v_00_u03b2_1969_, lean_object* v_b_1970_, lean_object* v_acc_1971_, lean_object* v_i_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__16_spec__22_spec__23(v_00_u03b2_1969_, v_b_1970_, v_acc_1971_, v_i_1972_);
lean_dec_ref(v_b_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1980_, lean_object* v_argsPacker_1981_, lean_object* v_preDefs_1982_){
_start:
{
uint8_t v___y_1984_; uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1980_);
if (v___x_2004_ == 0)
{
v___y_1984_ = v___x_2004_;
goto v___jp_1983_;
}
else
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1981_);
v___y_1984_ = v___x_2005_;
goto v___jp_1983_;
}
v___jp_1983_:
{
if (v___y_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1981_);
v___x_1987_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
lean_dec(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_declName_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1988_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_array_get_borrowed(v___x_1988_, v_preDefs_1982_, v___x_1989_);
v_declName_1991_ = lean_ctor_get(v___x_1990_, 3);
v___x_1992_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1991_);
v___x_1993_ = l_Lean_Name_append(v_declName_1991_, v___x_1992_);
return v___x_1993_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_declName_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1994_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_array_get_borrowed(v___x_1994_, v_preDefs_1982_, v___x_1995_);
v_declName_1997_ = lean_ctor_get(v___x_1996_, 3);
v___x_1998_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1997_);
v___x_1999_ = l_Lean_Name_append(v_declName_1997_, v___x_1998_);
return v___x_1999_;
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v_declName_2003_; 
v___x_2000_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = lean_array_get_borrowed(v___x_2000_, v_preDefs_1982_, v___x_2001_);
v_declName_2003_ = lean_ctor_get(v___x_2002_, 3);
lean_inc(v_declName_2003_);
return v_declName_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_2006_, lean_object* v_argsPacker_2007_, lean_object* v_preDefs_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2006_, v_argsPacker_2007_, v_preDefs_2008_);
lean_dec_ref(v_preDefs_2008_);
lean_dec_ref(v_argsPacker_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
v___x_2017_ = lean_apply_6(v_k_2010_, v_b_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, lean_box(0));
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_2018_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_2026_, lean_object* v_type_2027_, lean_object* v_k_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___f_2034_; lean_object* v___x_2035_; 
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2034_, 0, v_k_2028_);
v___x_2035_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_2026_, v_type_2027_, v___f_2034_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_a_2044_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2035_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2035_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_2052_, lean_object* v_type_2053_, lean_object* v_k_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2052_, v_type_2053_, v_k_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_2061_, lean_object* v_perm_2062_, lean_object* v_type_2063_, lean_object* v_k_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_2062_, v_type_2063_, v_k_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_2071_, lean_object* v_perm_2072_, lean_object* v_type_2073_, lean_object* v_k_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_2071_, v_perm_2072_, v_type_2073_, v_k_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_2081_, lean_object* v_ys_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_bs_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref(v_ys_2082_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v_bs_2085_);
return v___x_2092_;
}
else
{
lean_object* v_v_2093_; lean_object* v_value_2094_; lean_object* v___x_2095_; lean_object* v_bs_x27_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_v_2093_ = lean_array_uget_borrowed(v_bs_2085_, v_i_2084_);
v_value_2094_ = lean_ctor_get(v_v_2093_, 7);
lean_inc_ref(v_value_2094_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v_bs_x27_2096_ = lean_array_uset(v_bs_2085_, v_i_2084_, v___x_2095_);
v___x_2097_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2098_ = lean_usize_to_nat(v_i_2084_);
v___x_2099_ = lean_array_get_borrowed(v___x_2097_, v___x_2081_, v___x_2098_);
lean_dec(v___x_2098_);
lean_inc_ref(v_ys_2082_);
lean_inc(v___x_2099_);
v___x_2100_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2099_, v_value_2094_, v_ys_2082_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2084_, v___x_2102_);
v___x_2104_ = lean_array_uset(v_bs_x27_2096_, v_i_2084_, v_a_2101_);
v_i_2084_ = v___x_2103_;
v_bs_2085_ = v___x_2104_;
goto _start;
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v_bs_x27_2096_);
lean_dec_ref(v_ys_2082_);
v_a_2106_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2100_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2100_);
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
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2114_, lean_object* v_ys_2115_, lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_bs_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
size_t v_sz_boxed_2124_; size_t v_i_boxed_2125_; lean_object* v_res_2126_; 
v_sz_boxed_2124_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2125_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2114_, v_ys_2115_, v_sz_boxed_2124_, v_i_boxed_2125_, v_bs_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v___x_2114_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2127_, lean_object* v_ys_2128_, size_t v_sz_2129_, size_t v_i_2130_, lean_object* v_bs_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_usize_dec_lt(v_i_2130_, v_sz_2129_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v_ys_2128_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_bs_2131_);
return v___x_2138_;
}
else
{
lean_object* v_v_2139_; lean_object* v_type_2140_; lean_object* v___x_2141_; lean_object* v_bs_x27_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_v_2139_ = lean_array_uget_borrowed(v_bs_2131_, v_i_2130_);
v_type_2140_ = lean_ctor_get(v_v_2139_, 6);
lean_inc_ref(v_type_2140_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v_bs_x27_2142_ = lean_array_uset(v_bs_2131_, v_i_2130_, v___x_2141_);
v___x_2143_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2144_ = lean_usize_to_nat(v_i_2130_);
v___x_2145_ = lean_array_get_borrowed(v___x_2143_, v___x_2127_, v___x_2144_);
lean_dec(v___x_2144_);
lean_inc_ref(v_ys_2128_);
lean_inc(v___x_2145_);
v___x_2146_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2145_, v_type_2140_, v_ys_2128_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2130_, v___x_2148_);
v___x_2150_ = lean_array_uset(v_bs_x27_2142_, v_i_2130_, v_a_2147_);
v_i_2130_ = v___x_2149_;
v_bs_2131_ = v___x_2150_;
goto _start;
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref(v_bs_x27_2142_);
lean_dec_ref(v_ys_2128_);
v_a_2152_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2146_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2146_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2160_, lean_object* v_ys_2161_, lean_object* v_sz_2162_, lean_object* v_i_2163_, lean_object* v_bs_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
size_t v_sz_boxed_2170_; size_t v_i_boxed_2171_; lean_object* v_res_2172_; 
v_sz_boxed_2170_ = lean_unbox_usize(v_sz_2162_);
lean_dec(v_sz_2162_);
v_i_boxed_2171_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2160_, v_ys_2161_, v_sz_boxed_2170_, v_i_boxed_2171_, v_bs_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v___x_2160_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
if (lean_obj_tag(v_a_2173_) == 0)
{
lean_object* v___x_2175_; 
v___x_2175_ = l_List_reverse___redArg(v_a_2174_);
return v___x_2175_;
}
else
{
lean_object* v_head_2176_; lean_object* v_tail_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2186_; 
v_head_2176_ = lean_ctor_get(v_a_2173_, 0);
v_tail_2177_ = lean_ctor_get(v_a_2173_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_a_2173_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2179_ = v_a_2173_;
v_isShared_2180_ = v_isSharedCheck_2186_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_tail_2177_);
lean_inc(v_head_2176_);
lean_dec(v_a_2173_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2186_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = l_Lean_mkLevelParam(v_head_2176_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_a_2174_);
lean_ctor_set(v___x_2179_, 0, v___x_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_a_2174_);
v___x_2183_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
v_a_2173_ = v_tail_2177_;
v_a_2174_ = v___x_2183_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2187_, size_t v_i_2188_, lean_object* v_bs_2189_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_usize_dec_lt(v_i_2188_, v_sz_2187_);
if (v___x_2190_ == 0)
{
return v_bs_2189_;
}
else
{
lean_object* v_v_2191_; lean_object* v_declName_2192_; lean_object* v___x_2193_; lean_object* v_bs_x27_2194_; size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v_v_2191_ = lean_array_uget_borrowed(v_bs_2189_, v_i_2188_);
v_declName_2192_ = lean_ctor_get(v_v_2191_, 3);
lean_inc(v_declName_2192_);
v___x_2193_ = lean_unsigned_to_nat(0u);
v_bs_x27_2194_ = lean_array_uset(v_bs_2189_, v_i_2188_, v___x_2193_);
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2188_, v___x_2195_);
v___x_2197_ = lean_array_uset(v_bs_x27_2194_, v_i_2188_, v_declName_2192_);
v_i_2188_ = v___x_2196_;
v_bs_2189_ = v___x_2197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_bs_2201_){
_start:
{
size_t v_sz_boxed_2202_; size_t v_i_boxed_2203_; lean_object* v_res_2204_; 
v_sz_boxed_2202_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2203_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2202_, v_i_boxed_2203_, v_bs_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2205_, lean_object* v_perms_2206_, lean_object* v_argsPacker_2207_, uint8_t v___x_2208_, lean_object* v_ref_2209_, uint8_t v_kind_2210_, lean_object* v_levelParams_2211_, lean_object* v_modifiers_2212_, lean_object* v_newFn_2213_, lean_object* v_binders_2214_, lean_object* v_numSectionVars_2215_, lean_object* v_value_2216_, lean_object* v_termination_2217_, lean_object* v_fixedParamPerms_2218_, lean_object* v_ys_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
v_sz_2225_ = lean_array_size(v_preDefs_2205_);
v___x_2226_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2205_);
lean_inc_ref(v_ys_2219_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2206_, v_ys_2219_, v_sz_2225_, v___x_2226_, v_preDefs_2205_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
lean_inc_ref(v_preDefs_2205_);
lean_inc_ref(v_ys_2219_);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2206_, v_ys_2219_, v_sz_2225_, v___x_2226_, v_preDefs_2205_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2207_, v_a_2228_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v_a_2228_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; uint8_t v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = 1;
v___x_2234_ = 1;
v___x_2235_ = l_Lean_Meta_mkForallFVars(v_ys_2219_, v_a_2232_, v___x_2208_, v___x_2233_, v___x_2233_, v___x_2234_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_n(v_a_2236_, 2);
lean_dec_ref_known(v___x_2235_, 1);
lean_inc_ref(v_termination_2217_);
lean_inc(v_numSectionVars_2215_);
lean_inc(v_binders_2214_);
lean_inc(v_newFn_2213_);
lean_inc_ref(v_modifiers_2212_);
lean_inc(v_levelParams_2211_);
lean_inc(v_ref_2209_);
v___x_2237_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2237_, 0, v_ref_2209_);
lean_ctor_set(v___x_2237_, 1, v_levelParams_2211_);
lean_ctor_set(v___x_2237_, 2, v_modifiers_2212_);
lean_ctor_set(v___x_2237_, 3, v_newFn_2213_);
lean_ctor_set(v___x_2237_, 4, v_binders_2214_);
lean_ctor_set(v___x_2237_, 5, v_numSectionVars_2215_);
lean_ctor_set(v___x_2237_, 6, v_a_2236_);
lean_ctor_set(v___x_2237_, 7, v_value_2216_);
lean_ctor_set(v___x_2237_, 8, v_termination_2217_);
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*9, v_kind_2210_);
v___x_2238_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2237_, v___y_2222_, v___y_2223_);
lean_dec_ref_known(v___x_2237_, 9);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2239_; 
lean_dec_ref_known(v___x_2238_, 1);
v___x_2239_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2207_, v_a_2230_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v_a_2230_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = lean_box(0);
lean_inc(v_levelParams_2211_);
v___x_2242_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2211_, v___x_2241_);
lean_inc(v_newFn_2213_);
v___x_2243_ = l_Lean_mkConst(v_newFn_2213_, v___x_2242_);
v___x_2244_ = l_Lean_mkAppN(v___x_2243_, v_ys_2219_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2225_, v___x_2226_, v_preDefs_2205_);
v___x_2246_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2218_, v_argsPacker_2207_, v___x_2245_, v___x_2244_, v_a_2240_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = l_Lean_Meta_mkLambdaFVars(v_ys_2219_, v_a_2247_, v___x_2208_, v___x_2233_, v___x_2208_, v___x_2233_, v___x_2234_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec_ref(v_ys_2219_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2257_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2253_, 0, v_ref_2209_);
lean_ctor_set(v___x_2253_, 1, v_levelParams_2211_);
lean_ctor_set(v___x_2253_, 2, v_modifiers_2212_);
lean_ctor_set(v___x_2253_, 3, v_newFn_2213_);
lean_ctor_set(v___x_2253_, 4, v_binders_2214_);
lean_ctor_set(v___x_2253_, 5, v_numSectionVars_2215_);
lean_ctor_set(v___x_2253_, 6, v_a_2236_);
lean_ctor_set(v___x_2253_, 7, v_a_2249_);
lean_ctor_set(v___x_2253_, 8, v_termination_2217_);
lean_ctor_set_uint8(v___x_2253_, sizeof(void*)*9, v_kind_2210_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_a_2236_);
lean_dec_ref(v_termination_2217_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
v_a_2258_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2248_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2248_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2236_);
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_termination_2217_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
v_a_2266_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2246_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2246_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2236_);
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_fixedParamPerms_2218_);
lean_dec_ref(v_termination_2217_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
lean_dec_ref(v_argsPacker_2207_);
lean_dec_ref(v_preDefs_2205_);
v_a_2274_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2239_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2239_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2236_);
lean_dec(v_a_2230_);
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_fixedParamPerms_2218_);
lean_dec_ref(v_termination_2217_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
lean_dec_ref(v_argsPacker_2207_);
lean_dec_ref(v_preDefs_2205_);
v_a_2282_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2238_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2238_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2230_);
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_fixedParamPerms_2218_);
lean_dec_ref(v_termination_2217_);
lean_dec_ref(v_value_2216_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
lean_dec_ref(v_argsPacker_2207_);
lean_dec_ref(v_preDefs_2205_);
v_a_2290_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2235_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2235_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_a_2230_);
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_fixedParamPerms_2218_);
lean_dec_ref(v_termination_2217_);
lean_dec_ref(v_value_2216_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
lean_dec_ref(v_argsPacker_2207_);
lean_dec_ref(v_preDefs_2205_);
v_a_2298_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2231_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2231_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v_a_2228_);
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_fixedParamPerms_2218_);
lean_dec_ref(v_termination_2217_);
lean_dec_ref(v_value_2216_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
lean_dec_ref(v_argsPacker_2207_);
lean_dec_ref(v_preDefs_2205_);
v_a_2306_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2229_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2229_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_ys_2219_);
lean_dec_ref(v_fixedParamPerms_2218_);
lean_dec_ref(v_termination_2217_);
lean_dec_ref(v_value_2216_);
lean_dec(v_numSectionVars_2215_);
lean_dec(v_binders_2214_);
lean_dec(v_newFn_2213_);
lean_dec_ref(v_modifiers_2212_);
lean_dec(v_levelParams_2211_);
lean_dec(v_ref_2209_);
lean_dec_ref(v_argsPacker_2207_);
lean_dec_ref(v_preDefs_2205_);
v_a_2314_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2227_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2227_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2322_ = _args[0];
lean_object* v_perms_2323_ = _args[1];
lean_object* v_argsPacker_2324_ = _args[2];
lean_object* v___x_2325_ = _args[3];
lean_object* v_ref_2326_ = _args[4];
lean_object* v_kind_2327_ = _args[5];
lean_object* v_levelParams_2328_ = _args[6];
lean_object* v_modifiers_2329_ = _args[7];
lean_object* v_newFn_2330_ = _args[8];
lean_object* v_binders_2331_ = _args[9];
lean_object* v_numSectionVars_2332_ = _args[10];
lean_object* v_value_2333_ = _args[11];
lean_object* v_termination_2334_ = _args[12];
lean_object* v_fixedParamPerms_2335_ = _args[13];
lean_object* v_ys_2336_ = _args[14];
lean_object* v___y_2337_ = _args[15];
lean_object* v___y_2338_ = _args[16];
lean_object* v___y_2339_ = _args[17];
lean_object* v___y_2340_ = _args[18];
lean_object* v___y_2341_ = _args[19];
_start:
{
uint8_t v___x_2529__boxed_2342_; uint8_t v_kind_boxed_2343_; lean_object* v_res_2344_; 
v___x_2529__boxed_2342_ = lean_unbox(v___x_2325_);
v_kind_boxed_2343_ = lean_unbox(v_kind_2327_);
v_res_2344_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2322_, v_perms_2323_, v_argsPacker_2324_, v___x_2529__boxed_2342_, v_ref_2326_, v_kind_boxed_2343_, v_levelParams_2328_, v_modifiers_2329_, v_newFn_2330_, v_binders_2331_, v_numSectionVars_2332_, v_value_2333_, v_termination_2334_, v_fixedParamPerms_2335_, v_ys_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_perms_2323_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2345_, lean_object* v_argsPacker_2346_, lean_object* v_preDefs_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v_ref_2356_; uint8_t v_kind_2357_; lean_object* v_levelParams_2358_; lean_object* v_modifiers_2359_; lean_object* v_declName_2360_; lean_object* v_binders_2361_; lean_object* v_numSectionVars_2362_; lean_object* v_type_2363_; lean_object* v_value_2364_; lean_object* v_termination_2365_; lean_object* v_newFn_2366_; uint8_t v___x_2367_; 
v___x_2353_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_array_get_borrowed(v___x_2353_, v_preDefs_2347_, v___x_2354_);
v_ref_2356_ = lean_ctor_get(v___x_2355_, 0);
v_kind_2357_ = lean_ctor_get_uint8(v___x_2355_, sizeof(void*)*9);
v_levelParams_2358_ = lean_ctor_get(v___x_2355_, 1);
v_modifiers_2359_ = lean_ctor_get(v___x_2355_, 2);
v_declName_2360_ = lean_ctor_get(v___x_2355_, 3);
v_binders_2361_ = lean_ctor_get(v___x_2355_, 4);
v_numSectionVars_2362_ = lean_ctor_get(v___x_2355_, 5);
v_type_2363_ = lean_ctor_get(v___x_2355_, 6);
v_value_2364_ = lean_ctor_get(v___x_2355_, 7);
v_termination_2365_ = lean_ctor_get(v___x_2355_, 8);
lean_inc_ref(v_fixedParamPerms_2345_);
v_newFn_2366_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2345_, v_argsPacker_2346_, v_preDefs_2347_);
v___x_2367_ = lean_name_eq(v_newFn_2366_, v_declName_2360_);
if (v___x_2367_ == 0)
{
lean_object* v_perms_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_inc_ref(v_termination_2365_);
lean_inc_ref(v_value_2364_);
lean_inc_ref(v_type_2363_);
lean_inc(v_numSectionVars_2362_);
lean_inc(v_binders_2361_);
lean_inc_ref(v_modifiers_2359_);
lean_inc(v_levelParams_2358_);
lean_inc(v_ref_2356_);
v_perms_2368_ = lean_ctor_get(v_fixedParamPerms_2345_, 1);
lean_inc_ref_n(v_perms_2368_, 2);
v___x_2369_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2370_ = lean_box(v___x_2367_);
v___x_2371_ = lean_box(v_kind_2357_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2372_, 0, v_preDefs_2347_);
lean_closure_set(v___f_2372_, 1, v_perms_2368_);
lean_closure_set(v___f_2372_, 2, v_argsPacker_2346_);
lean_closure_set(v___f_2372_, 3, v___x_2370_);
lean_closure_set(v___f_2372_, 4, v_ref_2356_);
lean_closure_set(v___f_2372_, 5, v___x_2371_);
lean_closure_set(v___f_2372_, 6, v_levelParams_2358_);
lean_closure_set(v___f_2372_, 7, v_modifiers_2359_);
lean_closure_set(v___f_2372_, 8, v_newFn_2366_);
lean_closure_set(v___f_2372_, 9, v_binders_2361_);
lean_closure_set(v___f_2372_, 10, v_numSectionVars_2362_);
lean_closure_set(v___f_2372_, 11, v_value_2364_);
lean_closure_set(v___f_2372_, 12, v_termination_2365_);
lean_closure_set(v___f_2372_, 13, v_fixedParamPerms_2345_);
v___x_2373_ = lean_array_get(v___x_2369_, v_perms_2368_, v___x_2354_);
lean_dec_ref(v_perms_2368_);
v___x_2374_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2373_, v_type_2363_, v___f_2372_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; 
lean_inc(v___x_2355_);
lean_dec(v_newFn_2366_);
lean_dec_ref(v_preDefs_2347_);
lean_dec_ref(v_argsPacker_2346_);
lean_dec_ref(v_fixedParamPerms_2345_);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2355_);
return v___x_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2376_, lean_object* v_argsPacker_2377_, lean_object* v_preDefs_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2376_, v_argsPacker_2377_, v_preDefs_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2385_, lean_object* v_ys_2386_, lean_object* v_as_2387_, size_t v_sz_2388_, size_t v_i_2389_, lean_object* v_bs_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2385_, v_ys_2386_, v_sz_2388_, v_i_2389_, v_bs_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2397_, lean_object* v_ys_2398_, lean_object* v_as_2399_, lean_object* v_sz_2400_, lean_object* v_i_2401_, lean_object* v_bs_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
size_t v_sz_boxed_2408_; size_t v_i_boxed_2409_; lean_object* v_res_2410_; 
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2400_);
lean_dec(v_sz_2400_);
v_i_boxed_2409_ = lean_unbox_usize(v_i_2401_);
lean_dec(v_i_2401_);
v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2397_, v_ys_2398_, v_as_2399_, v_sz_boxed_2408_, v_i_boxed_2409_, v_bs_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v_as_2399_);
lean_dec_ref(v___x_2397_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2411_, lean_object* v_ys_2412_, lean_object* v_as_2413_, size_t v_sz_2414_, size_t v_i_2415_, lean_object* v_bs_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2411_, v_ys_2412_, v_sz_2414_, v_i_2415_, v_bs_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2423_, lean_object* v_ys_2424_, lean_object* v_as_2425_, lean_object* v_sz_2426_, lean_object* v_i_2427_, lean_object* v_bs_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
size_t v_sz_boxed_2434_; size_t v_i_boxed_2435_; lean_object* v_res_2436_; 
v_sz_boxed_2434_ = lean_unbox_usize(v_sz_2426_);
lean_dec(v_sz_2426_);
v_i_boxed_2435_ = lean_unbox_usize(v_i_2427_);
lean_dec(v_i_2427_);
v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2423_, v_ys_2424_, v_as_2425_, v_sz_boxed_2434_, v_i_boxed_2435_, v_bs_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_as_2425_);
lean_dec_ref(v___x_2423_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2437_, lean_object* v_k_2438_, uint8_t v_cleanupAnnotations_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___f_2445_; uint8_t v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2445_, 0, v_k_2438_);
v___x_2446_ = 1;
v___x_2447_ = 0;
v___x_2448_ = lean_box(0);
v___x_2449_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2437_, v___x_2446_, v___x_2447_, v___x_2446_, v___x_2447_, v___x_2448_, v___f_2445_, v_cleanupAnnotations_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2466_, lean_object* v_k_2467_, lean_object* v_cleanupAnnotations_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2474_; lean_object* v_res_2475_; 
v_cleanupAnnotations_boxed_2474_ = lean_unbox(v_cleanupAnnotations_2468_);
v_res_2475_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2466_, v_k_2467_, v_cleanupAnnotations_boxed_2474_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2476_, lean_object* v_e_2477_, lean_object* v_k_2478_, uint8_t v_cleanupAnnotations_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2477_, v_k_2478_, v_cleanupAnnotations_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2486_, lean_object* v_e_2487_, lean_object* v_k_2488_, lean_object* v_cleanupAnnotations_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2495_; lean_object* v_res_2496_; 
v_cleanupAnnotations_boxed_2495_ = lean_unbox(v_cleanupAnnotations_2489_);
v_res_2496_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2486_, v_e_2487_, v_k_2488_, v_cleanupAnnotations_boxed_2495_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___f_2503_; lean_object* v___x_1717__overap_2504_; lean_object* v___x_2505_; 
v___f_2503_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1717__overap_2504_ = lean_panic_fn_borrowed(v___f_2503_, v_msg_2497_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___y_2499_);
lean_inc_ref(v___y_2498_);
v___x_2505_ = lean_apply_5(v___x_1717__overap_2504_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, lean_box(0));
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_array_get_size(v_xs_2513_);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2522_, v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_x_2523_);
lean_dec_ref(v_xs_2522_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2530_, size_t v_sz_2531_, size_t v_i_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_a_2539_; uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_lt(v_i_2532_, v_sz_2531_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v_b_2533_);
return v___x_2544_;
}
else
{
lean_object* v_snd_2545_; lean_object* v_fst_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2590_; 
v_snd_2545_ = lean_ctor_get(v_b_2533_, 1);
v_fst_2546_ = lean_ctor_get(v_b_2533_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_b_2533_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2548_ = v_b_2533_;
v_isShared_2549_ = v_isSharedCheck_2590_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_snd_2545_);
lean_inc(v_fst_2546_);
lean_dec(v_b_2533_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2590_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_array_2550_; lean_object* v_start_2551_; lean_object* v_stop_2552_; uint8_t v___x_2553_; 
v_array_2550_ = lean_ctor_get(v_snd_2545_, 0);
v_start_2551_ = lean_ctor_get(v_snd_2545_, 1);
v_stop_2552_ = lean_ctor_get(v_snd_2545_, 2);
v___x_2553_ = lean_nat_dec_lt(v_start_2551_, v_stop_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2555_; 
if (v_isShared_2549_ == 0)
{
v___x_2555_ = v___x_2548_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_fst_2546_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_snd_2545_);
v___x_2555_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
}
else
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2586_; 
lean_inc(v_stop_2552_);
lean_inc(v_start_2551_);
lean_inc_ref(v_array_2550_);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_snd_2545_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; 
v_unused_2587_ = lean_ctor_get(v_snd_2545_, 2);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_snd_2545_, 1);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_snd_2545_, 0);
lean_dec(v_unused_2589_);
v___x_2559_ = v_snd_2545_;
v_isShared_2560_ = v_isSharedCheck_2586_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v_snd_2545_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2586_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2561_ = lean_array_fget(v_array_2550_, v_start_2551_);
v___x_2562_ = lean_unsigned_to_nat(1u);
v___x_2563_ = lean_nat_add(v_start_2551_, v___x_2562_);
lean_dec(v_start_2551_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2563_);
v___x_2565_ = v___x_2559_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_array_2550_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_stop_2552_);
v___x_2565_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_array_uget_borrowed(v_as_2530_, v_i_2532_);
v___x_2567_ = l_Lean_Expr_fvarId_x21(v_a_2566_);
v___x_2568_ = l_Lean_FVarId_getUserName___redArg(v___x_2567_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = lean_array_push(v_fst_2546_, v_a_2569_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v___x_2565_);
lean_ctor_set(v___x_2548_, 0, v___x_2570_);
v___x_2572_ = v___x_2548_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___x_2565_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
v_a_2539_ = v___x_2572_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v___x_2565_);
lean_del_object(v___x_2548_);
lean_dec(v_fst_2546_);
v_a_2574_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2568_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2568_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2561_, 1);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v___x_2565_);
v___x_2583_ = v___x_2548_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_fst_2546_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2565_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
v_a_2539_ = v___x_2583_;
goto v___jp_2538_;
}
}
}
}
}
}
}
v___jp_2538_:
{
size_t v___x_2540_; size_t v___x_2541_; 
v___x_2540_ = ((size_t)1ULL);
v___x_2541_ = lean_usize_add(v_i_2532_, v___x_2540_);
v_i_2532_ = v___x_2541_;
v_b_2533_ = v_a_2539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2591_, lean_object* v_sz_2592_, lean_object* v_i_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2592_);
lean_dec(v_sz_2592_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2593_);
lean_dec(v_i_2593_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2591_, v_sz_boxed_2599_, v_i_boxed_2600_, v_b_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v_as_2591_);
return v_res_2601_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2604_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2605_ = lean_unsigned_to_nat(4u);
v___x_2606_ = lean_unsigned_to_nat(119u);
v___x_2607_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2608_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2609_ = l_mkPanicMessageWithDecl(v___x_2608_, v___x_2607_, v___x_2606_, v___x_2605_, v___x_2604_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2611_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2612_ = lean_unsigned_to_nat(4u);
v___x_2613_ = lean_unsigned_to_nat(120u);
v___x_2614_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2615_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2616_ = l_mkPanicMessageWithDecl(v___x_2615_, v___x_2614_, v___x_2613_, v___x_2612_, v___x_2611_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2619_, lean_object* v_fixedParamPerms_2620_, lean_object* v_preDefIdx_2621_, lean_object* v_xs_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = lean_array_get_size(v_xs_2622_);
v___x_2630_ = lean_nat_dec_eq(v___x_2629_, v_a_2619_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2632_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2631_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2632_;
}
else
{
lean_object* v_perms_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_perms_2633_ = lean_ctor_get(v_fixedParamPerms_2620_, 1);
v___x_2634_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2635_ = lean_array_get_borrowed(v___x_2634_, v_perms_2633_, v_preDefIdx_2621_);
v___x_2636_ = lean_array_get_size(v___x_2635_);
v___x_2637_ = lean_nat_dec_eq(v___x_2636_, v_a_2619_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2639_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2638_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2639_;
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; size_t v_sz_2644_; size_t v___x_2645_; lean_object* v___x_2646_; 
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2635_);
v___x_2642_ = l_Array_toSubarray___redArg(v___x_2635_, v___x_2640_, v___x_2636_);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v_sz_2644_ = lean_array_size(v_xs_2622_);
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2622_, v_sz_2644_, v___x_2645_, v___x_2643_, v___y_2624_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2655_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2655_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2655_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_fst_2651_; lean_object* v___x_2653_; 
v_fst_2651_ = lean_ctor_get(v_a_2647_, 0);
lean_inc(v_fst_2651_);
lean_dec(v_a_2647_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v_fst_2651_);
v___x_2653_ = v___x_2649_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_fst_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
v_a_2656_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2646_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2646_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2664_, lean_object* v_fixedParamPerms_2665_, lean_object* v_preDefIdx_2666_, lean_object* v_xs_2667_, lean_object* v_x_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2664_, v_fixedParamPerms_2665_, v_preDefIdx_2666_, v_xs_2667_, v_x_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec_ref(v_x_2668_);
lean_dec_ref(v_xs_2667_);
lean_dec(v_preDefIdx_2666_);
lean_dec_ref(v_fixedParamPerms_2665_);
lean_dec(v_a_2664_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2676_, lean_object* v_preDefIdx_2677_, lean_object* v_preDef_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_type_2684_; lean_object* v_value_2685_; lean_object* v___f_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; 
v_type_2684_ = lean_ctor_get(v_preDef_2678_, 6);
lean_inc_ref(v_type_2684_);
v_value_2685_ = lean_ctor_get(v_preDef_2678_, 7);
lean_inc_ref(v_value_2685_);
lean_dec_ref(v_preDef_2678_);
v___f_2686_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2687_ = 0;
v___x_2688_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2685_, v___f_2686_, v___x_2687_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc_n(v_a_2689_, 2);
lean_dec_ref_known(v___x_2688_, 1);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2690_, 0, v_a_2689_);
lean_closure_set(v___f_2690_, 1, v_fixedParamPerms_2676_);
lean_closure_set(v___f_2690_, 2, v_preDefIdx_2677_);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_a_2689_);
v___x_2692_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2684_, v___x_2691_, v___f_2690_, v___x_2687_, v___x_2687_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
return v___x_2692_;
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v_type_2684_);
lean_dec(v_preDefIdx_2677_);
lean_dec_ref(v_fixedParamPerms_2676_);
v_a_2693_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2688_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2688_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2701_, lean_object* v_preDefIdx_2702_, lean_object* v_preDef_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2701_, v_preDefIdx_2702_, v_preDef_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2710_, size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2710_, v_sz_2711_, v_i_2712_, v_b_2713_, v___y_2714_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2720_, lean_object* v_sz_2721_, lean_object* v_i_2722_, lean_object* v_b_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
size_t v_sz_boxed_2729_; size_t v_i_boxed_2730_; lean_object* v_res_2731_; 
v_sz_boxed_2729_ = lean_unbox_usize(v_sz_2721_);
lean_dec(v_sz_2721_);
v_i_boxed_2730_ = lean_unbox_usize(v_i_2722_);
lean_dec(v_i_2722_);
v_res_2731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2720_, v_sz_boxed_2729_, v_i_boxed_2730_, v_b_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec_ref(v_as_2720_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___f_2738_; lean_object* v___x_1720__overap_2739_; lean_object* v___x_2740_; 
v___f_2738_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1720__overap_2739_ = lean_panic_fn_borrowed(v___f_2738_, v_msg_2732_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc_ref(v___y_2733_);
v___x_2740_ = lean_apply_5(v___x_1720__overap_2739_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2748_; double v___x_2749_; 
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = lean_float_of_nat(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_ref_2760_; lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2806_; 
v_ref_2760_ = lean_ctor_get(v___y_2757_, 5);
v___x_2761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2806_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2806_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v_traceState_2767_; lean_object* v_env_2768_; lean_object* v_nextMacroScope_2769_; lean_object* v_ngen_2770_; lean_object* v_auxDeclNGen_2771_; lean_object* v_cache_2772_; lean_object* v_messages_2773_; lean_object* v_infoState_2774_; lean_object* v_snapshotTasks_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2805_; 
v___x_2766_ = lean_st_ref_take(v___y_2758_);
v_traceState_2767_ = lean_ctor_get(v___x_2766_, 4);
v_env_2768_ = lean_ctor_get(v___x_2766_, 0);
v_nextMacroScope_2769_ = lean_ctor_get(v___x_2766_, 1);
v_ngen_2770_ = lean_ctor_get(v___x_2766_, 2);
v_auxDeclNGen_2771_ = lean_ctor_get(v___x_2766_, 3);
v_cache_2772_ = lean_ctor_get(v___x_2766_, 5);
v_messages_2773_ = lean_ctor_get(v___x_2766_, 6);
v_infoState_2774_ = lean_ctor_get(v___x_2766_, 7);
v_snapshotTasks_2775_ = lean_ctor_get(v___x_2766_, 8);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2777_ = v___x_2766_;
v_isShared_2778_ = v_isSharedCheck_2805_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_snapshotTasks_2775_);
lean_inc(v_infoState_2774_);
lean_inc(v_messages_2773_);
lean_inc(v_cache_2772_);
lean_inc(v_traceState_2767_);
lean_inc(v_auxDeclNGen_2771_);
lean_inc(v_ngen_2770_);
lean_inc(v_nextMacroScope_2769_);
lean_inc(v_env_2768_);
lean_dec(v___x_2766_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2805_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
uint64_t v_tid_2779_; lean_object* v_traces_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2804_; 
v_tid_2779_ = lean_ctor_get_uint64(v_traceState_2767_, sizeof(void*)*1);
v_traces_2780_ = lean_ctor_get(v_traceState_2767_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_traceState_2767_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2782_ = v_traceState_2767_;
v_isShared_2783_ = v_isSharedCheck_2804_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_traces_2780_);
lean_dec(v_traceState_2767_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2804_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; double v___x_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2786_ = 0;
v___x_2787_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2788_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2788_, 0, v_cls_2753_);
lean_ctor_set(v___x_2788_, 1, v___x_2784_);
lean_ctor_set(v___x_2788_, 2, v___x_2787_);
lean_ctor_set_float(v___x_2788_, sizeof(void*)*3, v___x_2785_);
lean_ctor_set_float(v___x_2788_, sizeof(void*)*3 + 8, v___x_2785_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*3 + 16, v___x_2786_);
v___x_2789_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2790_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v_a_2762_);
lean_ctor_set(v___x_2790_, 2, v___x_2789_);
lean_inc(v_ref_2760_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_ref_2760_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_PersistentArray_push___redArg(v_traces_2780_, v___x_2791_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2792_);
v___x_2794_ = v___x_2782_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2792_);
lean_ctor_set_uint64(v_reuseFailAlloc_2803_, sizeof(void*)*1, v_tid_2779_);
v___x_2794_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2796_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 4, v___x_2794_);
v___x_2796_ = v___x_2777_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_env_2768_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_nextMacroScope_2769_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v_ngen_2770_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_auxDeclNGen_2771_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2802_, 5, v_cache_2772_);
lean_ctor_set(v_reuseFailAlloc_2802_, 6, v_messages_2773_);
lean_ctor_set(v_reuseFailAlloc_2802_, 7, v_infoState_2774_);
lean_ctor_set(v_reuseFailAlloc_2802_, 8, v_snapshotTasks_2775_);
v___x_2796_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2797_ = lean_st_ref_put(v___y_2758_, v___x_2796_);
v___x_2798_ = lean_box(0);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2798_);
v___x_2800_ = v___x_2764_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2807_, lean_object* v_msg_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2807_, v_msg_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
return v_res_2814_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2818_ = lean_unsigned_to_nat(8u);
v___x_2819_ = lean_unsigned_to_nat(135u);
v___x_2820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2821_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2822_ = l_mkPanicMessageWithDecl(v___x_2821_, v___x_2820_, v___x_2819_, v___x_2818_, v___x_2817_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2823_, lean_object* v_unaryPreDefNonRec_2824_, lean_object* v___x_2825_, lean_object* v_us_2826_, lean_object* v_argsPacker_2827_, lean_object* v___x_2828_, lean_object* v_params_2829_, lean_object* v_x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = lean_array_get_size(v_params_2829_);
v___x_2837_ = lean_nat_dec_eq(v___x_2823_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v___x_2828_);
lean_dec(v_us_2826_);
lean_dec_ref(v_unaryPreDefNonRec_2824_);
v___x_2838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2839_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2838_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v___x_2839_;
}
else
{
lean_object* v_declName_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_declName_2840_ = lean_ctor_get(v_unaryPreDefNonRec_2824_, 3);
lean_inc(v_declName_2840_);
lean_dec_ref(v_unaryPreDefNonRec_2824_);
v___x_2841_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2825_, v_params_2829_);
v___x_2842_ = l_Lean_mkConst(v_declName_2840_, v_us_2826_);
v___x_2843_ = l_Lean_mkAppN(v___x_2842_, v___x_2841_);
lean_dec_ref(v___x_2841_);
v___x_2844_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2827_, v___x_2843_, v___x_2828_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2825_, v_params_2829_);
v___x_2847_ = l_Lean_Expr_beta(v_a_2845_, v___x_2846_);
v___x_2848_ = 0;
v___x_2849_ = 1;
v___x_2850_ = l_Lean_Meta_mkLambdaFVars(v_params_2829_, v___x_2847_, v___x_2848_, v___x_2837_, v___x_2848_, v___x_2837_, v___x_2849_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v___x_2850_;
}
else
{
return v___x_2844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2851_, lean_object* v_unaryPreDefNonRec_2852_, lean_object* v___x_2853_, lean_object* v_us_2854_, lean_object* v_argsPacker_2855_, lean_object* v___x_2856_, lean_object* v_params_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2851_, v_unaryPreDefNonRec_2852_, v___x_2853_, v_us_2854_, v_argsPacker_2855_, v___x_2856_, v_params_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v_x_2858_);
lean_dec_ref(v_params_2857_);
lean_dec_ref(v_argsPacker_2855_);
lean_dec_ref(v___x_2853_);
lean_dec(v___x_2851_);
return v_res_2864_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2877_ = l_Lean_Name_append(v___x_2876_, v___x_2875_);
return v___x_2877_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2880_ = l_Lean_stringToMessageData(v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2881_, lean_object* v_unaryPreDefNonRec_2882_, lean_object* v_us_2883_, lean_object* v_argsPacker_2884_, size_t v_sz_2885_, size_t v_i_2886_, lean_object* v_bs_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_usize_dec_lt(v_i_2886_, v_sz_2885_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
lean_dec_ref(v_argsPacker_2884_);
lean_dec(v_us_2883_);
lean_dec_ref(v_unaryPreDefNonRec_2882_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v_bs_2887_);
return v___x_2894_;
}
else
{
lean_object* v_v_2895_; lean_object* v_perms_2896_; lean_object* v_ref_2897_; uint8_t v_kind_2898_; lean_object* v_levelParams_2899_; lean_object* v_modifiers_2900_; lean_object* v_declName_2901_; lean_object* v_binders_2902_; lean_object* v_numSectionVars_2903_; lean_object* v_type_2904_; lean_object* v_termination_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2956_; 
v_v_2895_ = lean_array_uget(v_bs_2887_, v_i_2886_);
v_perms_2896_ = lean_ctor_get(v_fixedParamPerms_2881_, 1);
v_ref_2897_ = lean_ctor_get(v_v_2895_, 0);
v_kind_2898_ = lean_ctor_get_uint8(v_v_2895_, sizeof(void*)*9);
v_levelParams_2899_ = lean_ctor_get(v_v_2895_, 1);
v_modifiers_2900_ = lean_ctor_get(v_v_2895_, 2);
v_declName_2901_ = lean_ctor_get(v_v_2895_, 3);
v_binders_2902_ = lean_ctor_get(v_v_2895_, 4);
v_numSectionVars_2903_ = lean_ctor_get(v_v_2895_, 5);
v_type_2904_ = lean_ctor_get(v_v_2895_, 6);
v_termination_2905_ = lean_ctor_get(v_v_2895_, 8);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_v_2895_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; 
v_unused_2957_ = lean_ctor_get(v_v_2895_, 7);
lean_dec(v_unused_2957_);
v___x_2907_ = v_v_2895_;
v_isShared_2908_ = v_isSharedCheck_2956_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_termination_2905_);
lean_inc(v_type_2904_);
lean_inc(v_numSectionVars_2903_);
lean_inc(v_binders_2902_);
lean_inc(v_declName_2901_);
lean_inc(v_modifiers_2900_);
lean_inc(v_levelParams_2899_);
lean_inc(v_ref_2897_);
lean_dec(v_v_2895_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2956_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v_bs_x27_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; lean_object* v___x_2918_; 
v___x_2909_ = lean_unsigned_to_nat(0u);
v_bs_x27_2910_ = lean_array_uset(v_bs_2887_, v_i_2886_, v___x_2909_);
v___x_2911_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2912_ = lean_usize_to_nat(v_i_2886_);
v___x_2913_ = lean_array_get_borrowed(v___x_2911_, v_perms_2896_, v___x_2912_);
v___x_2914_ = lean_array_get_size(v___x_2913_);
lean_inc_ref(v_argsPacker_2884_);
lean_inc(v_us_2883_);
lean_inc(v___x_2913_);
lean_inc_ref(v_unaryPreDefNonRec_2882_);
v___f_2915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2915_, 0, v___x_2914_);
lean_closure_set(v___f_2915_, 1, v_unaryPreDefNonRec_2882_);
lean_closure_set(v___f_2915_, 2, v___x_2913_);
lean_closure_set(v___f_2915_, 3, v_us_2883_);
lean_closure_set(v___f_2915_, 4, v_argsPacker_2884_);
lean_closure_set(v___f_2915_, 5, v___x_2912_);
v___x_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
v___x_2917_ = 0;
lean_inc_ref(v_type_2904_);
v___x_2918_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2904_, v___x_2916_, v___f_2915_, v___x_2917_, v___x_2917_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v_options_2928_; uint8_t v_hasTrace_2929_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v_options_2928_ = lean_ctor_get(v___y_2890_, 2);
v_hasTrace_2929_ = lean_ctor_get_uint8(v_options_2928_, sizeof(void*)*1);
if (v_hasTrace_2929_ == 0)
{
goto v___jp_2920_;
}
else
{
lean_object* v_inheritedTraceOptions_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_inheritedTraceOptions_2930_ = lean_ctor_get(v___y_2890_, 13);
v___x_2931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2932_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2933_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2930_, v_options_2928_, v___x_2932_);
if (v___x_2933_ == 0)
{
goto v___jp_2920_;
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_inc(v_declName_2901_);
v___x_2934_ = l_Lean_MessageData_ofName(v_declName_2901_);
v___x_2935_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
lean_inc(v_a_2919_);
v___x_2937_ = l_Lean_MessageData_ofExpr(v_a_2919_);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2931_, v___x_2938_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_dec_ref_known(v___x_2939_, 1);
goto v___jp_2920_;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2919_);
lean_dec_ref(v_bs_x27_2910_);
lean_del_object(v___x_2907_);
lean_dec_ref(v_termination_2905_);
lean_dec_ref(v_type_2904_);
lean_dec(v_numSectionVars_2903_);
lean_dec(v_binders_2902_);
lean_dec(v_declName_2901_);
lean_dec_ref(v_modifiers_2900_);
lean_dec(v_levelParams_2899_);
lean_dec(v_ref_2897_);
lean_dec_ref(v_argsPacker_2884_);
lean_dec(v_us_2883_);
lean_dec_ref(v_unaryPreDefNonRec_2882_);
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
v___jp_2920_:
{
lean_object* v___x_2922_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 7, v_a_2919_);
v___x_2922_ = v___x_2907_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_ref_2897_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_levelParams_2899_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_modifiers_2900_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_declName_2901_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v_binders_2902_);
lean_ctor_set(v_reuseFailAlloc_2927_, 5, v_numSectionVars_2903_);
lean_ctor_set(v_reuseFailAlloc_2927_, 6, v_type_2904_);
lean_ctor_set(v_reuseFailAlloc_2927_, 7, v_a_2919_);
lean_ctor_set(v_reuseFailAlloc_2927_, 8, v_termination_2905_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*9, v_kind_2898_);
v___x_2922_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_add(v_i_2886_, v___x_2923_);
v___x_2925_ = lean_array_uset(v_bs_x27_2910_, v_i_2886_, v___x_2922_);
v_i_2886_ = v___x_2924_;
v_bs_2887_ = v___x_2925_;
goto _start;
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_bs_x27_2910_);
lean_del_object(v___x_2907_);
lean_dec_ref(v_termination_2905_);
lean_dec_ref(v_type_2904_);
lean_dec(v_numSectionVars_2903_);
lean_dec(v_binders_2902_);
lean_dec(v_declName_2901_);
lean_dec_ref(v_modifiers_2900_);
lean_dec(v_levelParams_2899_);
lean_dec(v_ref_2897_);
lean_dec_ref(v_argsPacker_2884_);
lean_dec(v_us_2883_);
lean_dec_ref(v_unaryPreDefNonRec_2882_);
v_a_2948_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2918_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2918_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2958_, lean_object* v_unaryPreDefNonRec_2959_, lean_object* v_us_2960_, lean_object* v_argsPacker_2961_, lean_object* v_sz_2962_, lean_object* v_i_2963_, lean_object* v_bs_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
size_t v_sz_boxed_2970_; size_t v_i_boxed_2971_; lean_object* v_res_2972_; 
v_sz_boxed_2970_ = lean_unbox_usize(v_sz_2962_);
lean_dec(v_sz_2962_);
v_i_boxed_2971_ = lean_unbox_usize(v_i_2963_);
lean_dec(v_i_2963_);
v_res_2972_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2958_, v_unaryPreDefNonRec_2959_, v_us_2960_, v_argsPacker_2961_, v_sz_boxed_2970_, v_i_boxed_2971_, v_bs_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_fixedParamPerms_2958_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2973_, lean_object* v_preDefs_2974_, lean_object* v_fixedParamPerms_2975_, lean_object* v_us_2976_, lean_object* v_argsPacker_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2973_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_2983_) == 0)
{
size_t v_sz_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
lean_dec_ref_known(v___x_2983_, 1);
v_sz_2984_ = lean_array_size(v_preDefs_2974_);
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2975_, v_unaryPreDefNonRec_2973_, v_us_2976_, v_argsPacker_2977_, v_sz_2984_, v___x_2985_, v_preDefs_2974_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_2986_;
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec_ref(v_argsPacker_2977_);
lean_dec(v_us_2976_);
lean_dec_ref(v_preDefs_2974_);
lean_dec_ref(v_unaryPreDefNonRec_2973_);
v_a_2987_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2983_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2983_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2995_, lean_object* v_preDefs_2996_, lean_object* v_fixedParamPerms_2997_, lean_object* v_us_2998_, lean_object* v_argsPacker_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2995_, v_preDefs_2996_, v_fixedParamPerms_2997_, v_us_2998_, v_argsPacker_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v_fixedParamPerms_2997_);
return v_res_3005_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3006_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_3012_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
lean_ctor_set(v___x_3012_, 2, v___x_3011_);
lean_ctor_set(v___x_3012_, 3, v___x_3011_);
lean_ctor_set(v___x_3012_, 4, v___x_3011_);
lean_ctor_set(v___x_3012_, 5, v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v_nextMacroScope_3018_; lean_object* v_ngen_3019_; lean_object* v_auxDeclNGen_3020_; lean_object* v_traceState_3021_; lean_object* v_messages_3022_; lean_object* v_infoState_3023_; lean_object* v_snapshotTasks_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3050_; 
v___x_3017_ = lean_st_ref_take(v___y_3015_);
v_nextMacroScope_3018_ = lean_ctor_get(v___x_3017_, 1);
v_ngen_3019_ = lean_ctor_get(v___x_3017_, 2);
v_auxDeclNGen_3020_ = lean_ctor_get(v___x_3017_, 3);
v_traceState_3021_ = lean_ctor_get(v___x_3017_, 4);
v_messages_3022_ = lean_ctor_get(v___x_3017_, 6);
v_infoState_3023_ = lean_ctor_get(v___x_3017_, 7);
v_snapshotTasks_3024_ = lean_ctor_get(v___x_3017_, 8);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; lean_object* v_unused_3052_; 
v_unused_3051_ = lean_ctor_get(v___x_3017_, 5);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v___x_3017_, 0);
lean_dec(v_unused_3052_);
v___x_3026_ = v___x_3017_;
v_isShared_3027_ = v_isSharedCheck_3050_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_snapshotTasks_3024_);
lean_inc(v_infoState_3023_);
lean_inc(v_messages_3022_);
lean_inc(v_traceState_3021_);
lean_inc(v_auxDeclNGen_3020_);
lean_inc(v_ngen_3019_);
lean_inc(v_nextMacroScope_3018_);
lean_dec(v___x_3017_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3050_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 5, v___x_3028_);
lean_ctor_set(v___x_3026_, 0, v_env_3013_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_env_3013_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_nextMacroScope_3018_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_ngen_3019_);
lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_auxDeclNGen_3020_);
lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_traceState_3021_);
lean_ctor_set(v_reuseFailAlloc_3049_, 5, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3049_, 6, v_messages_3022_);
lean_ctor_set(v_reuseFailAlloc_3049_, 7, v_infoState_3023_);
lean_ctor_set(v_reuseFailAlloc_3049_, 8, v_snapshotTasks_3024_);
v___x_3030_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v_mctx_3033_; lean_object* v_zetaDeltaFVarIds_3034_; lean_object* v_postponed_3035_; lean_object* v_diag_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3047_; 
v___x_3031_ = lean_st_ref_put(v___y_3015_, v___x_3030_);
v___x_3032_ = lean_st_ref_take(v___y_3014_);
v_mctx_3033_ = lean_ctor_get(v___x_3032_, 0);
v_zetaDeltaFVarIds_3034_ = lean_ctor_get(v___x_3032_, 2);
v_postponed_3035_ = lean_ctor_get(v___x_3032_, 3);
v_diag_3036_ = lean_ctor_get(v___x_3032_, 4);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3032_, 1);
lean_dec(v_unused_3048_);
v___x_3038_ = v___x_3032_;
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_diag_3036_);
lean_inc(v_postponed_3035_);
lean_inc(v_zetaDeltaFVarIds_3034_);
lean_inc(v_mctx_3033_);
lean_dec(v___x_3032_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3040_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 1, v___x_3040_);
v___x_3042_ = v___x_3038_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_mctx_3033_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_zetaDeltaFVarIds_3034_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_postponed_3035_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v_diag_3036_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_st_ref_put(v___y_3014_, v___x_3042_);
v___x_3044_ = lean_box(0);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3053_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
lean_dec(v___y_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v_env_3066_; lean_object* v_a_3068_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3065_ = lean_st_ref_get(v___y_3063_);
v_env_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc_ref(v_env_3066_);
lean_dec(v___x_3065_);
v___x_3078_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3058_, v___y_3061_, v___y_3063_);
lean_dec_ref(v___x_3078_);
lean_inc(v___y_3063_);
lean_inc_ref(v___y_3062_);
lean_inc(v___y_3061_);
lean_inc_ref(v___y_3060_);
v___x_3079_ = lean_apply_5(v_x_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, lean_box(0));
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3066_, v___y_3061_, v___y_3063_);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3088_ == 0)
{
lean_object* v_unused_3089_; 
v_unused_3089_ = lean_ctor_get(v___x_3081_, 0);
lean_dec(v_unused_3089_);
v___x_3083_ = v___x_3081_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_dec(v___x_3081_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v_a_3080_);
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3080_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
else
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3079_, 1);
v_a_3068_ = v_a_3090_;
goto v___jp_3067_;
}
v___jp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v___x_3069_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3066_, v___y_3061_, v___y_3063_);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_3069_, 0);
lean_dec(v_unused_3077_);
v___x_3071_ = v___x_3069_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v___x_3069_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 1);
lean_ctor_set(v___x_3071_, 0, v_a_3068_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3068_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3091_, v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3099_, lean_object* v_argsPacker_3100_, lean_object* v_preDefs_3101_, lean_object* v_unaryPreDefNonRec_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v___x_3108_; lean_object* v_levelParams_3109_; lean_object* v_env_3110_; lean_object* v___x_3111_; lean_object* v_us_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3108_ = lean_st_ref_get(v_a_3106_);
v_levelParams_3109_ = lean_ctor_get(v_unaryPreDefNonRec_3102_, 1);
v_env_3110_ = lean_ctor_get(v___x_3108_, 0);
lean_inc_ref(v_env_3110_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
lean_inc(v_levelParams_3109_);
v_us_3112_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3109_, v___x_3111_);
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3113_, 0, v_unaryPreDefNonRec_3102_);
lean_closure_set(v___f_3113_, 1, v_preDefs_3101_);
lean_closure_set(v___f_3113_, 2, v_fixedParamPerms_3099_);
lean_closure_set(v___f_3113_, 3, v_us_3112_);
lean_closure_set(v___f_3113_, 4, v_argsPacker_3100_);
v___x_3114_ = l_Lean_Environment_unlockAsync(v_env_3110_);
v___x_3115_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3114_, v___f_3113_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3116_, lean_object* v_argsPacker_3117_, lean_object* v_preDefs_3118_, lean_object* v_unaryPreDefNonRec_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3116_, v_argsPacker_3117_, v_preDefs_3118_, v_unaryPreDefNonRec_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3126_, lean_object* v_unaryPreDefNonRec_3127_, lean_object* v_us_3128_, lean_object* v_argsPacker_3129_, lean_object* v_as_3130_, size_t v_sz_3131_, size_t v_i_3132_, lean_object* v_bs_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3126_, v_unaryPreDefNonRec_3127_, v_us_3128_, v_argsPacker_3129_, v_sz_3131_, v_i_3132_, v_bs_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3140_, lean_object* v_unaryPreDefNonRec_3141_, lean_object* v_us_3142_, lean_object* v_argsPacker_3143_, lean_object* v_as_3144_, lean_object* v_sz_3145_, lean_object* v_i_3146_, lean_object* v_bs_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
size_t v_sz_boxed_3153_; size_t v_i_boxed_3154_; lean_object* v_res_3155_; 
v_sz_boxed_3153_ = lean_unbox_usize(v_sz_3145_);
lean_dec(v_sz_3145_);
v_i_boxed_3154_ = lean_unbox_usize(v_i_3146_);
lean_dec(v_i_3146_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3140_, v_unaryPreDefNonRec_3141_, v_us_3142_, v_argsPacker_3143_, v_as_3144_, v_sz_boxed_3153_, v_i_boxed_3154_, v_bs_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v_as_3144_);
lean_dec_ref(v_fixedParamPerms_3140_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3156_, v___y_3158_, v___y_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3170_, lean_object* v_env_3171_, lean_object* v_x_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3171_, v_x_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_env_3180_, lean_object* v_x_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3179_, v_env_3180_, v_x_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3187_;
}
}
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
}
#ifdef __cplusplus
}
#endif
