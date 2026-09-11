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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
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
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object*);
uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object*);
uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Elab.PreDefinition.WF.PackMutual"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.WF.packCalls"};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_packCalls___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "assertion violation: fidx < fixedParamPerms.perms.size\n      "};
static const lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_WF_packCalls___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_packCalls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_packCalls___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_packCalls___closed__0 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__0_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__1;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Not a forall: "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__2 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__2_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__3;
static const lean_string_object l_Lean_Elab_WF_packCalls___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_WF_packCalls___closed__4 = (const lean_object*)&l_Lean_Elab_WF_packCalls___closed__4_value;
static lean_once_cell_t l_Lean_Elab_WF_packCalls___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_packCalls___closed__5;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_toCold_95_; lean_object* v_mctx_96_; lean_object* v_lctx_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_88_);
v_toCold_95_ = lean_ctor_get(v___y_89_, 0);
v_mctx_96_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_96_);
lean_dec(v___x_94_);
v_lctx_97_ = lean_ctor_get(v___y_87_, 2);
v_options_98_ = lean_ctor_get(v_toCold_95_, 2);
lean_inc_ref(v_options_98_);
lean_inc_ref(v_lctx_97_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v_env_93_);
lean_ctor_set(v___x_99_, 1, v_mctx_96_);
lean_ctor_set(v___x_99_, 2, v_lctx_97_);
lean_ctor_set(v___x_99_, 3, v_options_98_);
v___x_100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_msgData_86_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0___boxed(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 2);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_ref_115_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_115_);
lean_ctor_set(v___x_121_, 1, v_a_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 1);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg___boxed(lean_object* v_msg_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_132_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_Elab_WF_withAppN___lam__0___closed__0));
v___x_135_ = l_Lean_stringToMessageData(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0(lean_object* v_args_136_, lean_object* v_k_137_, uint8_t v___x_138_, lean_object* v_missing_139_, lean_object* v_xs_140_, lean_object* v_x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_array_get_size(v_xs_140_);
v___x_155_ = lean_nat_dec_lt(v___x_154_, v_missing_139_);
if (v___x_155_ == 0)
{
goto v___jp_147_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
lean_dec_ref(v_k_137_);
lean_dec_ref(v_args_136_);
v___x_156_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___lam__0___closed__1, &l_Lean_Elab_WF_withAppN___lam__0___closed__1_once, _init_l_Lean_Elab_WF_withAppN___lam__0___closed__1);
v___x_157_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_156_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
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
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
v___jp_147_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Array_append___redArg(v_args_136_, v_xs_140_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc_ref(v___y_142_);
v___x_149_ = lean_apply_6(v_k_137_, v___x_148_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, lean_box(0));
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; uint8_t v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v___x_149_, 1);
v___x_151_ = 1;
v___x_152_ = 1;
v___x_153_ = l_Lean_Meta_mkLambdaFVars(v_xs_140_, v_a_150_, v___x_138_, v___x_151_, v___x_138_, v___x_151_, v___x_152_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
return v___x_153_;
}
else
{
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object* v_args_166_, lean_object* v_k_167_, lean_object* v___x_168_, lean_object* v_missing_169_, lean_object* v_xs_170_, lean_object* v_x_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
uint8_t v___x_2226__boxed_177_; lean_object* v_res_178_; 
v___x_2226__boxed_177_ = lean_unbox(v___x_168_);
v_res_178_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_166_, v_k_167_, v___x_2226__boxed_177_, v_missing_169_, v_xs_170_, v_x_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v_x_171_);
lean_dec_ref(v_xs_170_);
lean_dec(v_missing_169_);
return v_res_178_;
}
}
static lean_object* _init_l_Lean_Elab_WF_withAppN___closed__0(void){
_start:
{
lean_object* v___x_179_; lean_object* v_dummy_180_; 
v___x_179_ = lean_box(0);
v_dummy_180_ = l_Lean_Expr_sort___override(v___x_179_);
return v_dummy_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN(lean_object* v_n_181_, lean_object* v_e_182_, lean_object* v_k_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_dummy_189_; lean_object* v_nargs_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_args_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_dummy_189_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_190_ = l_Lean_Expr_getAppNumArgs(v_e_182_);
lean_inc(v_nargs_190_);
v___x_191_ = lean_mk_array(v_nargs_190_, v_dummy_189_);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_sub(v_nargs_190_, v___x_192_);
lean_dec(v_nargs_190_);
lean_inc_ref(v_e_182_);
v_args_194_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_182_, v___x_191_, v___x_193_);
v___x_195_ = lean_array_get_size(v_args_194_);
v___x_196_ = lean_nat_dec_le(v_n_181_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_inc(v_a_187_);
lean_inc_ref(v_a_186_);
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
v___x_197_ = lean_infer_type(v_e_182_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_209_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_209_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_missing_202_; lean_object* v___x_203_; lean_object* v___f_204_; lean_object* v___x_206_; 
v_missing_202_ = lean_nat_sub(v_n_181_, v___x_195_);
lean_dec(v_n_181_);
v___x_203_ = lean_box(v___x_196_);
lean_inc(v_missing_202_);
v___f_204_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_withAppN___lam__0___boxed), 11, 4);
lean_closure_set(v___f_204_, 0, v_args_194_);
lean_closure_set(v___f_204_, 1, v_k_183_);
lean_closure_set(v___f_204_, 2, v___x_203_);
lean_closure_set(v___f_204_, 3, v_missing_202_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 1);
lean_ctor_set(v___x_200_, 0, v_missing_202_);
v___x_206_ = v___x_200_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_missing_202_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_a_198_, v___x_206_, v___f_204_, v___x_196_, v___x_196_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_207_;
}
}
}
else
{
lean_dec_ref(v_args_194_);
lean_dec_ref(v_k_183_);
lean_dec(v_n_181_);
return v___x_197_;
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v_e_182_);
v___x_210_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_181_);
lean_inc_ref(v_args_194_);
v___x_211_ = l_Array_toSubarray___redArg(v_args_194_, v___x_210_, v_n_181_);
v___x_212_ = l_Subarray_copy___redArg(v___x_211_);
lean_inc(v_a_187_);
lean_inc_ref(v_a_186_);
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
v___x_213_ = lean_apply_6(v_k_183_, v___x_212_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_228_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_228_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_lower_219_; lean_object* v_upper_220_; uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_le(v_n_181_, v___x_210_);
if (v___x_227_ == 0)
{
v_lower_219_ = v_n_181_;
v_upper_220_ = v___x_195_;
goto v___jp_218_;
}
else
{
lean_dec(v_n_181_);
v_lower_219_ = v___x_210_;
v_upper_220_ = v___x_195_;
goto v___jp_218_;
}
v___jp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_221_ = l_Array_toSubarray___redArg(v_args_194_, v_lower_219_, v_upper_220_);
v___x_222_ = l_Subarray_copy___redArg(v___x_221_);
v___x_223_ = l_Lean_mkAppN(v_a_214_, v___x_222_);
lean_dec_ref(v___x_222_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_223_);
v___x_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_dec_ref(v_args_194_);
lean_dec(v_n_181_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___boxed(lean_object* v_n_229_, lean_object* v_e_230_, lean_object* v_k_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Elab_WF_withAppN(v_n_229_, v_e_230_, v_k_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(lean_object* v_00_u03b1_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___boxed(lean_object* v_00_u03b1_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0(v_00_u03b1_246_, v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1(lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_1209__overap_262_; lean_object* v___x_263_; 
v___f_261_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1209__overap_262_ = lean_panic_fn_borrowed(v___f_261_, v_msg_255_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
lean_inc(v___y_257_);
lean_inc_ref(v___y_256_);
v___x_263_ = lean_apply_5(v___x_1209__overap_262_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, lean_box(0));
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__0___closed__0));
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__0___boxed(lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_WF_packCalls___lam__0(v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec_ref(v_x_281_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1(lean_object* v___x_288_, lean_object* v_argsPacker_289_, lean_object* v___x_290_, lean_object* v_val_291_, lean_object* v_newF_292_, lean_object* v_args_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_288_, v_args_293_);
v___x_300_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_289_, v___x_290_, v_val_291_, v___x_299_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec_ref(v___x_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_309_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_309_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_Expr_app___override(v_newF_292_, v_a_301_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_dec_ref(v_newF_292_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__1___boxed(lean_object* v___x_310_, lean_object* v_argsPacker_311_, lean_object* v___x_312_, lean_object* v_val_313_, lean_object* v_newF_314_, lean_object* v_args_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Elab_WF_packCalls___lam__1(v___x_310_, v_argsPacker_311_, v___x_312_, v_val_313_, v_newF_314_, v_args_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec_ref(v_args_315_);
lean_dec_ref(v_argsPacker_311_);
lean_dec_ref(v___x_310_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(lean_object* v_xs_322_, lean_object* v_v_323_, lean_object* v_i_324_){
_start:
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_array_get_size(v_xs_322_);
v___x_326_ = lean_nat_dec_lt(v_i_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec(v_i_324_);
v___x_327_ = lean_box(0);
return v___x_327_;
}
else
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_array_fget_borrowed(v_xs_322_, v_i_324_);
v___x_329_ = lean_name_eq(v___x_328_, v_v_323_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_i_324_, v___x_330_);
lean_dec(v_i_324_);
v_i_324_ = v___x_331_;
goto _start;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_i_324_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2___boxed(lean_object* v_xs_334_, lean_object* v_v_335_, lean_object* v_i_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_334_, v_v_335_, v_i_336_);
lean_dec(v_v_335_);
lean_dec_ref(v_xs_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(lean_object* v_xs_338_, lean_object* v_v_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0_spec__2(v_xs_338_, v_v_339_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0___boxed(lean_object* v_xs_342_, lean_object* v_v_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_342_, v_v_343_);
lean_dec(v_v_343_);
lean_dec_ref(v_xs_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(lean_object* v_xs_345_, lean_object* v_v_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0_spec__0(v_xs_345_, v_v_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v_val_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_val_349_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_347_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_val_349_);
lean_dec(v___x_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_val_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0___boxed(lean_object* v_xs_357_, lean_object* v_v_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_xs_357_, v_v_358_);
lean_dec(v_v_358_);
lean_dec_ref(v_xs_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(lean_object* v_val_360_, lean_object* v___x_361_, size_t v_sz_362_, size_t v_i_363_, lean_object* v_bs_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_usize_dec_lt(v_i_363_, v_sz_362_);
if (v___x_365_ == 0)
{
return v_bs_364_;
}
else
{
lean_object* v_v_366_; lean_object* v___x_367_; lean_object* v_bs_x27_368_; uint8_t v___y_370_; 
v_v_366_ = lean_array_uget(v_bs_364_, v_i_363_);
v___x_367_ = lean_unsigned_to_nat(0u);
v_bs_x27_368_ = lean_array_uset(v_bs_364_, v_i_363_, v___x_367_);
if (lean_obj_tag(v_v_366_) == 0)
{
uint8_t v___x_376_; 
v___x_376_ = 0;
v___y_370_ = v___x_376_;
goto v___jp_369_;
}
else
{
uint8_t v___x_377_; 
lean_dec_ref_known(v_v_366_, 1);
v___x_377_ = lean_nat_dec_lt(v_val_360_, v___x_361_);
v___y_370_ = v___x_377_;
goto v___jp_369_;
}
v___jp_369_:
{
size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_363_, v___x_371_);
v___x_373_ = lean_box(v___y_370_);
v___x_374_ = lean_array_uset(v_bs_x27_368_, v_i_363_, v___x_373_);
v_i_363_ = v___x_372_;
v_bs_364_ = v___x_374_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object* v_val_378_, lean_object* v___x_379_, lean_object* v_sz_380_, lean_object* v_i_381_, lean_object* v_bs_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_380_);
lean_dec(v_sz_380_);
v_i_boxed_384_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_378_, v___x_379_, v_sz_boxed_383_, v_i_boxed_384_, v_bs_382_);
lean_dec(v___x_379_);
lean_dec(v_val_378_);
return v_res_385_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__2));
v___x_390_ = lean_unsigned_to_nat(6u);
v___x_391_ = lean_unsigned_to_nat(55u);
v___x_392_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__1));
v___x_393_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_394_ = l_mkPanicMessageWithDecl(v___x_393_, v___x_392_, v___x_391_, v___x_390_, v___x_389_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object* v_funNames_395_, lean_object* v_fixedParamPerms_396_, lean_object* v___x_397_, lean_object* v_argsPacker_398_, lean_object* v___x_399_, lean_object* v_newF_400_, lean_object* v_e_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = l_Lean_Expr_getAppFn(v_e_401_);
v___x_408_ = l_Lean_Expr_isConst(v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref(v___x_407_);
lean_dec_ref(v_newF_400_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v_argsPacker_398_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_e_401_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l_Lean_Expr_constName_x21(v___x_407_);
lean_dec_ref(v___x_407_);
v___x_412_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_funNames_395_, v___x_411_);
lean_dec(v___x_411_);
if (lean_obj_tag(v___x_412_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_448_; 
v_val_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_448_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_448_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_448_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_perms_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_perms_417_ = lean_ctor_get(v_fixedParamPerms_396_, 1);
v___x_418_ = lean_array_get_size(v_perms_417_);
v___x_419_ = lean_nat_dec_lt(v_val_413_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_del_object(v___x_415_);
lean_dec(v_val_413_);
lean_dec_ref(v_e_401_);
lean_dec_ref(v_newF_400_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v_argsPacker_398_);
v___x_420_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__3, &l_Lean_Elab_WF_packCalls___lam__2___closed__3_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3);
v___x_421_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v___x_420_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___f_423_; size_t v_sz_424_; size_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_422_ = lean_array_get_borrowed(v___x_397_, v_perms_417_, v_val_413_);
lean_inc(v_val_413_);
lean_inc_n(v___x_422_, 2);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_423_, 0, v___x_422_);
lean_closure_set(v___f_423_, 1, v_argsPacker_398_);
lean_closure_set(v___f_423_, 2, v___x_399_);
lean_closure_set(v___f_423_, 3, v_val_413_);
lean_closure_set(v___f_423_, 4, v_newF_400_);
v_sz_424_ = lean_array_size(v___x_422_);
v___x_425_ = ((size_t)0ULL);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v_val_413_, v___x_418_, v_sz_424_, v___x_425_, v___x_422_);
lean_dec(v_val_413_);
v___x_427_ = lean_array_get_size(v___x_426_);
lean_dec_ref(v___x_426_);
v___x_428_ = l_Lean_Elab_WF_withAppN(v___x_427_, v_e_401_, v___f_423_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_439_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_439_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 0);
lean_ctor_set(v___x_415_, 0, v_a_429_);
v___x_434_ = v___x_415_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_434_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_del_object(v___x_415_);
v_a_440_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_428_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_428_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v___x_412_);
lean_dec_ref(v_newF_400_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v_argsPacker_398_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_e_401_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2___boxed(lean_object* v_funNames_451_, lean_object* v_fixedParamPerms_452_, lean_object* v___x_453_, lean_object* v_argsPacker_454_, lean_object* v___x_455_, lean_object* v_newF_456_, lean_object* v_e_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_WF_packCalls___lam__2(v_funNames_451_, v_fixedParamPerms_452_, v___x_453_, v_argsPacker_454_, v___x_455_, v_newF_456_, v_e_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v___x_453_);
lean_dec_ref(v_fixedParamPerms_452_);
lean_dec_ref(v_funNames_451_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_object* v_00_u03b1_464_, lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_apply_1(v_x_465_, lean_box(0));
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0___boxed(lean_object* v_00_u03b1_473_, lean_object* v_x_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(v_00_u03b1_473_, v_x_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_480_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = l_Lean_maxRecDepthErrorMessage;
v___x_487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
v___x_489_ = l_Lean_MessageData_ofFormat(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
v___x_491_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2));
v___x_492_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object* v_ref_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v_ref_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object* v_ref_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___y_509_; lean_object* v_toCold_518_; lean_object* v_currRecDepth_519_; lean_object* v_ref_520_; uint8_t v_diag_521_; uint8_t v_suppressElabErrors_522_; lean_object* v_maxRecDepth_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_toCold_518_ = lean_ctor_get(v___y_505_, 0);
v_currRecDepth_519_ = lean_ctor_get(v___y_505_, 1);
v_ref_520_ = lean_ctor_get(v___y_505_, 2);
v_diag_521_ = lean_ctor_get_uint8(v___y_505_, sizeof(void*)*3);
v_suppressElabErrors_522_ = lean_ctor_get_uint8(v___y_505_, sizeof(void*)*3 + 1);
v_maxRecDepth_528_ = lean_ctor_get(v_toCold_518_, 3);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_nat_dec_eq(v_maxRecDepth_528_, v___x_529_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
v___x_531_ = lean_nat_dec_eq(v_currRecDepth_519_, v_maxRecDepth_528_);
if (v___x_531_ == 0)
{
goto v___jp_523_;
}
else
{
lean_object* v___x_532_; 
lean_dec_ref(v_x_501_);
lean_inc(v_ref_520_);
v___x_532_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_520_);
v___y_509_ = v___x_532_;
goto v___jp_508_;
}
}
else
{
goto v___jp_523_;
}
v___jp_508_:
{
if (lean_obj_tag(v___y_509_) == 0)
{
return v___y_509_;
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_a_510_ = lean_ctor_get(v___y_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___y_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___y_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___y_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
v___jp_523_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_nat_add(v_currRecDepth_519_, v___x_524_);
lean_inc(v_ref_520_);
lean_inc_ref(v_toCold_518_);
v___x_526_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_526_, 0, v_toCold_518_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
lean_ctor_set(v___x_526_, 2, v_ref_520_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*3, v_diag_521_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*3 + 1, v_suppressElabErrors_522_);
lean_inc(v___y_506_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
v___x_527_ = lean_apply_6(v_x_501_, v___y_502_, v___y_503_, v___y_504_, v___x_526_, v___y_506_, lean_box(0));
v___y_509_ = v___x_527_;
goto v___jp_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_541_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_555_, lean_object* v___y_556_, lean_object* v_b_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; 
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_556_);
v___x_563_ = lean_apply_7(v_k_555_, v_b_557_, v___y_556_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, lean_box(0));
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_564_, lean_object* v___y_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_564_, v___y_565_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_565_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_573_, lean_object* v_type_574_, lean_object* v_val_575_, lean_object* v_k_576_, uint8_t v_nondep_577_, uint8_t v_kind_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___f_585_; lean_object* v___x_586_; 
lean_inc(v___y_579_);
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_585_, 0, v_k_576_);
lean_closure_set(v___f_585_, 1, v___y_579_);
v___x_586_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_573_, v_type_574_, v_val_575_, v___f_585_, v_nondep_577_, v_kind_578_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_586_) == 0)
{
return v___x_586_;
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_595_, lean_object* v_type_596_, lean_object* v_val_597_, lean_object* v_k_598_, lean_object* v_nondep_599_, lean_object* v_kind_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v_nondep_boxed_607_; uint8_t v_kind_boxed_608_; lean_object* v_res_609_; 
v_nondep_boxed_607_ = lean_unbox(v_nondep_599_);
v_kind_boxed_608_ = lean_unbox(v_kind_600_);
v_res_609_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_595_, v_type_596_, v_val_597_, v_k_598_, v_nondep_boxed_607_, v_kind_boxed_608_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_610_, uint8_t v_bi_611_, lean_object* v_type_612_, lean_object* v_k_613_, uint8_t v_kind_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___f_621_; lean_object* v___x_622_; 
lean_inc(v___y_615_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_621_, 0, v_k_613_);
lean_closure_set(v___f_621_, 1, v___y_615_);
v___x_622_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_610_, v_bi_611_, v_type_612_, v___f_621_, v_kind_614_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_622_) == 0)
{
return v___x_622_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_631_, lean_object* v_bi_632_, lean_object* v_type_633_, lean_object* v_k_634_, lean_object* v_kind_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
uint8_t v_bi_boxed_642_; uint8_t v_kind_boxed_643_; lean_object* v_res_644_; 
v_bi_boxed_642_ = lean_unbox(v_bi_632_);
v_kind_boxed_643_ = lean_unbox(v_kind_635_);
v_res_644_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_631_, v_bi_boxed_642_, v_type_633_, v_k_634_, v_kind_boxed_643_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_645_, lean_object* v_x_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_apply_1(v_x_646_, lean_box(0));
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_654_, v_x_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v_key_665_; lean_object* v_value_666_; lean_object* v_tail_667_; uint8_t v___x_668_; 
v_key_665_ = lean_ctor_get(v_x_663_, 0);
v_value_666_ = lean_ctor_get(v_x_663_, 1);
v_tail_667_ = lean_ctor_get(v_x_663_, 2);
v___x_668_ = l_Lean_ExprStructEq_beq(v_key_665_, v_a_662_);
if (v___x_668_ == 0)
{
v_x_663_ = v_tail_667_;
goto _start;
}
else
{
lean_object* v___x_670_; 
lean_inc(v_value_666_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_value_666_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec_ref(v_a_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_buckets_676_; lean_object* v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v_fold_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_buckets_676_ = lean_ctor_get(v_m_674_, 1);
v___x_677_ = lean_array_get_size(v_buckets_676_);
v___x_678_ = l_Lean_ExprStructEq_hash(v_a_675_);
v___x_679_ = 32ULL;
v___x_680_ = lean_uint64_shift_right(v___x_678_, v___x_679_);
v_fold_681_ = lean_uint64_xor(v___x_678_, v___x_680_);
v___x_682_ = 16ULL;
v___x_683_ = lean_uint64_shift_right(v_fold_681_, v___x_682_);
v___x_684_ = lean_uint64_xor(v_fold_681_, v___x_683_);
v___x_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = lean_usize_of_nat(v___x_677_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_sub(v___x_686_, v___x_687_);
v___x_689_ = lean_usize_land(v___x_685_, v___x_688_);
v___x_690_ = lean_array_uget_borrowed(v_buckets_676_, v___x_689_);
v___x_691_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_675_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_692_, v_a_693_);
lean_dec_ref(v_a_693_);
lean_dec_ref(v_m_692_);
return v_res_694_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
else
{
lean_object* v_key_698_; lean_object* v_tail_699_; uint8_t v___x_700_; 
v_key_698_ = lean_ctor_get(v_x_696_, 0);
v_tail_699_ = lean_ctor_get(v_x_696_, 2);
v___x_700_ = l_Lean_ExprStructEq_beq(v_key_698_, v_a_695_);
if (v___x_700_ == 0)
{
v_x_696_ = v_tail_699_;
goto _start;
}
else
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_702_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_a_702_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
return v_x_706_;
}
else
{
lean_object* v_key_708_; lean_object* v_value_709_; lean_object* v_tail_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_733_; 
v_key_708_ = lean_ctor_get(v_x_707_, 0);
v_value_709_ = lean_ctor_get(v_x_707_, 1);
v_tail_710_ = lean_ctor_get(v_x_707_, 2);
v_isSharedCheck_733_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_733_ == 0)
{
v___x_712_ = v_x_707_;
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_tail_710_);
lean_inc(v_value_709_);
lean_inc(v_key_708_);
lean_dec(v_x_707_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v_fold_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; size_t v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_714_ = lean_array_get_size(v_x_706_);
v___x_715_ = l_Lean_ExprStructEq_hash(v_key_708_);
v___x_716_ = 32ULL;
v___x_717_ = lean_uint64_shift_right(v___x_715_, v___x_716_);
v_fold_718_ = lean_uint64_xor(v___x_715_, v___x_717_);
v___x_719_ = 16ULL;
v___x_720_ = lean_uint64_shift_right(v_fold_718_, v___x_719_);
v___x_721_ = lean_uint64_xor(v_fold_718_, v___x_720_);
v___x_722_ = lean_uint64_to_usize(v___x_721_);
v___x_723_ = lean_usize_of_nat(v___x_714_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_sub(v___x_723_, v___x_724_);
v___x_726_ = lean_usize_land(v___x_722_, v___x_725_);
v___x_727_ = lean_array_uget_borrowed(v_x_706_, v___x_726_);
lean_inc(v___x_727_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 2, v___x_727_);
v___x_729_ = v___x_712_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_key_708_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_value_709_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v___x_727_);
v___x_729_ = v_reuseFailAlloc_732_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_array_uset(v_x_706_, v___x_726_, v___x_729_);
v_x_706_ = v___x_730_;
v_x_707_ = v_tail_710_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_734_, lean_object* v_source_735_, lean_object* v_target_736_){
_start:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_array_get_size(v_source_735_);
v___x_738_ = lean_nat_dec_lt(v_i_734_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec_ref(v_source_735_);
lean_dec(v_i_734_);
return v_target_736_;
}
else
{
lean_object* v_es_739_; lean_object* v___x_740_; lean_object* v_source_741_; lean_object* v_target_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_es_739_ = lean_array_fget(v_source_735_, v_i_734_);
v___x_740_ = lean_box(0);
v_source_741_ = lean_array_fset(v_source_735_, v_i_734_, v___x_740_);
v_target_742_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_736_, v_es_739_);
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_i_734_, v___x_743_);
lean_dec(v_i_734_);
v_i_734_ = v___x_744_;
v_source_735_ = v_source_741_;
v_target_736_ = v_target_742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_nbuckets_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_747_ = lean_array_get_size(v_data_746_);
v___x_748_ = lean_unsigned_to_nat(2u);
v_nbuckets_749_ = lean_nat_mul(v___x_747_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_box(0);
v___x_752_ = lean_mk_array(v_nbuckets_749_, v___x_751_);
v___x_753_ = lean_array_propagate_mark(v_data_746_, v___x_752_);
v___x_754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_750_, v_data_746_, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_755_, lean_object* v_b_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_dec(v_b_756_);
lean_dec_ref(v_a_755_);
return v_x_757_;
}
else
{
lean_object* v_key_758_; lean_object* v_value_759_; lean_object* v_tail_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_772_; 
v_key_758_ = lean_ctor_get(v_x_757_, 0);
v_value_759_ = lean_ctor_get(v_x_757_, 1);
v_tail_760_ = lean_ctor_get(v_x_757_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_772_ == 0)
{
v___x_762_ = v_x_757_;
v_isShared_763_ = v_isSharedCheck_772_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_tail_760_);
lean_inc(v_value_759_);
lean_inc(v_key_758_);
lean_dec(v_x_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_772_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; 
v___x_764_ = l_Lean_ExprStructEq_beq(v_key_758_, v_a_755_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_755_, v_b_756_, v_tail_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 2, v___x_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_key_758_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_value_759_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_770_; 
lean_dec(v_value_759_);
lean_dec(v_key_758_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v_b_756_);
lean_ctor_set(v___x_762_, 0, v_a_755_);
v___x_770_ = v___x_762_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_755_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_b_756_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_tail_760_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_773_, lean_object* v_a_774_, lean_object* v_b_775_){
_start:
{
lean_object* v_size_776_; lean_object* v_buckets_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_820_; 
v_size_776_ = lean_ctor_get(v_m_773_, 0);
v_buckets_777_ = lean_ctor_get(v_m_773_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_m_773_);
if (v_isSharedCheck_820_ == 0)
{
v___x_779_ = v_m_773_;
v_isShared_780_ = v_isSharedCheck_820_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_buckets_777_);
lean_inc(v_size_776_);
lean_dec(v_m_773_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_820_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v_fold_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_bkt_794_; uint8_t v___x_795_; 
v___x_781_ = lean_array_get_size(v_buckets_777_);
v___x_782_ = l_Lean_ExprStructEq_hash(v_a_774_);
v___x_783_ = 32ULL;
v___x_784_ = lean_uint64_shift_right(v___x_782_, v___x_783_);
v_fold_785_ = lean_uint64_xor(v___x_782_, v___x_784_);
v___x_786_ = 16ULL;
v___x_787_ = lean_uint64_shift_right(v_fold_785_, v___x_786_);
v___x_788_ = lean_uint64_xor(v_fold_785_, v___x_787_);
v___x_789_ = lean_uint64_to_usize(v___x_788_);
v___x_790_ = lean_usize_of_nat(v___x_781_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_sub(v___x_790_, v___x_791_);
v___x_793_ = lean_usize_land(v___x_789_, v___x_792_);
v_bkt_794_ = lean_array_uget_borrowed(v_buckets_777_, v___x_793_);
v___x_795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_774_, v_bkt_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v_size_x27_797_; lean_object* v___x_798_; lean_object* v_buckets_x27_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v_size_x27_797_ = lean_nat_add(v_size_776_, v___x_796_);
lean_dec(v_size_776_);
lean_inc(v_bkt_794_);
v___x_798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_798_, 0, v_a_774_);
lean_ctor_set(v___x_798_, 1, v_b_775_);
lean_ctor_set(v___x_798_, 2, v_bkt_794_);
v_buckets_x27_799_ = lean_array_uset(v_buckets_777_, v___x_793_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(4u);
v___x_801_ = lean_nat_mul(v_size_x27_797_, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(3u);
v___x_803_ = lean_nat_div(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_array_get_size(v_buckets_x27_799_);
v___x_805_ = lean_nat_dec_le(v___x_803_, v___x_804_);
lean_dec(v___x_803_);
if (v___x_805_ == 0)
{
lean_object* v_val_806_; lean_object* v___x_808_; 
v_val_806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_799_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_val_806_);
lean_ctor_set(v___x_779_, 0, v_size_x27_797_);
v___x_808_ = v___x_779_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_size_x27_797_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_811_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_buckets_x27_799_);
lean_ctor_set(v___x_779_, 0, v_size_x27_797_);
v___x_811_ = v___x_779_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_buckets_x27_799_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v___x_813_; lean_object* v_buckets_x27_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_inc(v_bkt_794_);
v___x_813_ = lean_box(0);
v_buckets_x27_814_ = lean_array_uset(v_buckets_777_, v___x_793_, v___x_813_);
v___x_815_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_774_, v_b_775_, v_bkt_794_);
v___x_816_ = lean_array_uset(v_buckets_x27_814_, v___x_793_, v___x_815_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_816_);
v___x_818_ = v___x_779_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_size_776_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_821_, lean_object* v_e_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = lean_st_ref_take(v_a_821_);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_825_, v_e_822_, v_a_823_);
v___x_827_ = lean_st_ref_put(v_a_821_, v___x_826_);
v___x_828_ = lean_box(0);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_829_, lean_object* v_e_830_, lean_object* v_a_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_829_, v_e_830_, v_a_831_);
lean_dec(v_a_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_837_, lean_object* v_pre_838_, lean_object* v_post_839_, uint8_t v_usedLetOnly_840_, uint8_t v_skipConstInApp_841_, uint8_t v_skipInstances_842_, lean_object* v_body_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_array_push(v_fvars_837_, v_x_844_);
v___x_852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_838_, v_post_839_, v_usedLetOnly_840_, v_skipConstInApp_841_, v_skipInstances_842_, v___x_851_, v_body_843_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_853_, lean_object* v_pre_854_, lean_object* v_post_855_, lean_object* v_usedLetOnly_856_, lean_object* v_skipConstInApp_857_, lean_object* v_skipInstances_858_, lean_object* v_body_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v_usedLetOnly_boxed_867_; uint8_t v_skipConstInApp_boxed_868_; uint8_t v_skipInstances_boxed_869_; lean_object* v_res_870_; 
v_usedLetOnly_boxed_867_ = lean_unbox(v_usedLetOnly_856_);
v_skipConstInApp_boxed_868_ = lean_unbox(v_skipConstInApp_857_);
v_skipInstances_boxed_869_ = lean_unbox(v_skipInstances_858_);
v_res_870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_853_, v_pre_854_, v_post_855_, v_usedLetOnly_boxed_867_, v_skipConstInApp_boxed_868_, v_skipInstances_boxed_869_, v_body_859_, v_x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_871_, lean_object* v_post_872_, uint8_t v_usedLetOnly_873_, uint8_t v_skipConstInApp_874_, uint8_t v_skipInstances_875_, lean_object* v_e_876_, lean_object* v_a_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
lean_inc_ref(v_post_872_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc_ref(v_e_876_);
v___x_883_ = lean_apply_6(v_post_872_, v_e_876_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, lean_box(0));
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_902_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_902_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_902_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_902_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
switch(lean_obj_tag(v_a_884_))
{
case 0:
{
lean_object* v_e_888_; lean_object* v___x_890_; 
lean_dec_ref(v_e_876_);
lean_dec_ref(v_post_872_);
lean_dec_ref(v_pre_871_);
v_e_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc_ref(v_e_888_);
lean_dec_ref_known(v_a_884_, 1);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_e_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_e_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
case 1:
{
lean_object* v_e_892_; lean_object* v___x_893_; 
lean_del_object(v___x_886_);
lean_dec_ref(v_e_876_);
v_e_892_ = lean_ctor_get(v_a_884_, 0);
lean_inc_ref(v_e_892_);
lean_dec_ref_known(v_a_884_, 1);
v___x_893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_871_, v_post_872_, v_usedLetOnly_873_, v_skipConstInApp_874_, v_skipInstances_875_, v_e_892_, v_a_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_893_;
}
default: 
{
lean_object* v_e_x3f_894_; 
lean_dec_ref(v_post_872_);
lean_dec_ref(v_pre_871_);
v_e_x3f_894_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_e_x3f_894_);
lean_dec_ref_known(v_a_884_, 1);
if (lean_obj_tag(v_e_x3f_894_) == 0)
{
lean_object* v___x_896_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_e_876_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_e_876_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v_val_898_; lean_object* v___x_900_; 
lean_dec_ref(v_e_876_);
v_val_898_ = lean_ctor_get(v_e_x3f_894_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v_e_x3f_894_, 1);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_val_898_);
v___x_900_ = v___x_886_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_val_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_e_876_);
lean_dec_ref(v_post_872_);
lean_dec_ref(v_pre_871_);
v_a_903_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_883_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_883_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_911_, lean_object* v_post_912_, uint8_t v_usedLetOnly_913_, uint8_t v_skipConstInApp_914_, uint8_t v_skipInstances_915_, lean_object* v_fvars_916_, lean_object* v_e_917_, lean_object* v_a_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
if (lean_obj_tag(v_e_917_) == 6)
{
lean_object* v_binderName_924_; lean_object* v_binderType_925_; lean_object* v_body_926_; uint8_t v_binderInfo_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_binderName_924_ = lean_ctor_get(v_e_917_, 0);
lean_inc(v_binderName_924_);
v_binderType_925_ = lean_ctor_get(v_e_917_, 1);
lean_inc_ref(v_binderType_925_);
v_body_926_ = lean_ctor_get(v_e_917_, 2);
lean_inc_ref(v_body_926_);
v_binderInfo_927_ = lean_ctor_get_uint8(v_e_917_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_917_, 3);
v___x_928_ = lean_expr_instantiate_rev(v_binderType_925_, v_fvars_916_);
lean_dec_ref(v_binderType_925_);
lean_inc_ref(v_post_912_);
lean_inc_ref(v_pre_911_);
v___x_929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_911_, v_post_912_, v_usedLetOnly_913_, v_skipConstInApp_914_, v_skipInstances_915_, v___x_928_, v_a_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___f_934_; uint8_t v___x_935_; lean_object* v___x_936_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = lean_box(v_usedLetOnly_913_);
v___x_932_ = lean_box(v_skipConstInApp_914_);
v___x_933_ = lean_box(v_skipInstances_915_);
v___f_934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_934_, 0, v_fvars_916_);
lean_closure_set(v___f_934_, 1, v_pre_911_);
lean_closure_set(v___f_934_, 2, v_post_912_);
lean_closure_set(v___f_934_, 3, v___x_931_);
lean_closure_set(v___f_934_, 4, v___x_932_);
lean_closure_set(v___f_934_, 5, v___x_933_);
lean_closure_set(v___f_934_, 6, v_body_926_);
v___x_935_ = 0;
v___x_936_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_924_, v_binderInfo_927_, v_a_930_, v___f_934_, v___x_935_, v_a_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_936_;
}
else
{
lean_dec_ref(v_body_926_);
lean_dec(v_binderName_924_);
lean_dec_ref(v_fvars_916_);
lean_dec_ref(v_post_912_);
lean_dec_ref(v_pre_911_);
return v___x_929_;
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_expr_instantiate_rev(v_e_917_, v_fvars_916_);
lean_dec_ref(v_e_917_);
lean_inc_ref(v_post_912_);
lean_inc_ref(v_pre_911_);
v___x_938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_911_, v_post_912_, v_usedLetOnly_913_, v_skipConstInApp_914_, v_skipInstances_915_, v___x_937_, v_a_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; uint8_t v___x_940_; uint8_t v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v___x_940_ = 0;
v___x_941_ = 1;
v___x_942_ = 1;
v___x_943_ = l_Lean_Meta_mkLambdaFVars(v_fvars_916_, v_a_939_, v___x_940_, v_usedLetOnly_913_, v___x_940_, v___x_941_, v___x_942_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec_ref(v_fvars_916_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_911_, v_post_912_, v_usedLetOnly_913_, v_skipConstInApp_914_, v_skipInstances_915_, v_a_944_, v_a_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_945_;
}
else
{
lean_dec_ref(v_post_912_);
lean_dec_ref(v_pre_911_);
return v___x_943_;
}
}
else
{
lean_dec_ref(v_fvars_916_);
lean_dec_ref(v_post_912_);
lean_dec_ref(v_pre_911_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_946_, lean_object* v_pre_947_, lean_object* v_post_948_, uint8_t v_usedLetOnly_949_, uint8_t v_skipConstInApp_950_, uint8_t v_skipInstances_951_, lean_object* v_body_952_, lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_array_push(v_fvars_946_, v_x_953_);
v___x_961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_947_, v_post_948_, v_usedLetOnly_949_, v_skipConstInApp_950_, v_skipInstances_951_, v___x_960_, v_body_952_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_962_, lean_object* v_pre_963_, lean_object* v_post_964_, lean_object* v_usedLetOnly_965_, lean_object* v_skipConstInApp_966_, lean_object* v_skipInstances_967_, lean_object* v_body_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v_usedLetOnly_boxed_976_; uint8_t v_skipConstInApp_boxed_977_; uint8_t v_skipInstances_boxed_978_; lean_object* v_res_979_; 
v_usedLetOnly_boxed_976_ = lean_unbox(v_usedLetOnly_965_);
v_skipConstInApp_boxed_977_ = lean_unbox(v_skipConstInApp_966_);
v_skipInstances_boxed_978_ = lean_unbox(v_skipInstances_967_);
v_res_979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_962_, v_pre_963_, v_post_964_, v_usedLetOnly_boxed_976_, v_skipConstInApp_boxed_977_, v_skipInstances_boxed_978_, v_body_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_980_, lean_object* v_post_981_, uint8_t v_usedLetOnly_982_, uint8_t v_skipConstInApp_983_, uint8_t v_skipInstances_984_, lean_object* v_fvars_985_, lean_object* v_e_986_, lean_object* v_a_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
if (lean_obj_tag(v_e_986_) == 8)
{
lean_object* v_declName_993_; lean_object* v_type_994_; lean_object* v_value_995_; lean_object* v_body_996_; uint8_t v_nondep_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_declName_993_ = lean_ctor_get(v_e_986_, 0);
lean_inc(v_declName_993_);
v_type_994_ = lean_ctor_get(v_e_986_, 1);
lean_inc_ref(v_type_994_);
v_value_995_ = lean_ctor_get(v_e_986_, 2);
lean_inc_ref(v_value_995_);
v_body_996_ = lean_ctor_get(v_e_986_, 3);
lean_inc_ref(v_body_996_);
v_nondep_997_ = lean_ctor_get_uint8(v_e_986_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_986_, 4);
v___x_998_ = lean_expr_instantiate_rev(v_type_994_, v_fvars_985_);
lean_dec_ref(v_type_994_);
lean_inc_ref(v_post_981_);
lean_inc_ref(v_pre_980_);
v___x_999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_980_, v_post_981_, v_usedLetOnly_982_, v_skipConstInApp_983_, v_skipInstances_984_, v___x_998_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = lean_expr_instantiate_rev(v_value_995_, v_fvars_985_);
lean_dec_ref(v_value_995_);
lean_inc_ref(v_post_981_);
lean_inc_ref(v_pre_980_);
v___x_1002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_980_, v_post_981_, v_usedLetOnly_982_, v_skipConstInApp_983_, v_skipInstances_984_, v___x_1001_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = lean_box(v_usedLetOnly_982_);
v___x_1005_ = lean_box(v_skipConstInApp_983_);
v___x_1006_ = lean_box(v_skipInstances_984_);
v___f_1007_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1007_, 0, v_fvars_985_);
lean_closure_set(v___f_1007_, 1, v_pre_980_);
lean_closure_set(v___f_1007_, 2, v_post_981_);
lean_closure_set(v___f_1007_, 3, v___x_1004_);
lean_closure_set(v___f_1007_, 4, v___x_1005_);
lean_closure_set(v___f_1007_, 5, v___x_1006_);
lean_closure_set(v___f_1007_, 6, v_body_996_);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_993_, v_a_1000_, v_a_1003_, v___f_1007_, v_nondep_997_, v___x_1008_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
return v___x_1009_;
}
else
{
lean_dec(v_a_1000_);
lean_dec_ref(v_body_996_);
lean_dec(v_declName_993_);
lean_dec_ref(v_fvars_985_);
lean_dec_ref(v_post_981_);
lean_dec_ref(v_pre_980_);
return v___x_1002_;
}
}
else
{
lean_dec_ref(v_body_996_);
lean_dec_ref(v_value_995_);
lean_dec(v_declName_993_);
lean_dec_ref(v_fvars_985_);
lean_dec_ref(v_post_981_);
lean_dec_ref(v_pre_980_);
return v___x_999_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_expr_instantiate_rev(v_e_986_, v_fvars_985_);
lean_dec_ref(v_e_986_);
lean_inc_ref(v_post_981_);
lean_inc_ref(v_pre_980_);
v___x_1011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_980_, v_post_981_, v_usedLetOnly_982_, v_skipConstInApp_983_, v_skipInstances_984_, v___x_1010_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = 0;
v___x_1014_ = 1;
v___x_1015_ = l_Lean_Meta_mkLetFVars(v_fvars_985_, v_a_1012_, v_usedLetOnly_982_, v___x_1013_, v___x_1014_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec_ref(v_fvars_985_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_980_, v_post_981_, v_usedLetOnly_982_, v_skipConstInApp_983_, v_skipInstances_984_, v_a_1016_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
return v___x_1017_;
}
else
{
lean_dec_ref(v_post_981_);
lean_dec_ref(v_pre_980_);
return v___x_1015_;
}
}
else
{
lean_dec_ref(v_fvars_985_);
lean_dec_ref(v_post_981_);
lean_dec_ref(v_pre_980_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1018_, lean_object* v_post_1019_, uint8_t v_usedLetOnly_1020_, uint8_t v_skipConstInApp_1021_, uint8_t v_skipInstances_1022_, size_t v_sz_1023_, size_t v_i_1024_, lean_object* v_bs_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_lt(v_i_1024_, v_sz_1023_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_post_1019_);
lean_dec_ref(v_pre_1018_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_bs_1025_);
return v___x_1033_;
}
else
{
lean_object* v_v_1034_; lean_object* v___x_1035_; 
v_v_1034_ = lean_array_uget_borrowed(v_bs_1025_, v_i_1024_);
lean_inc(v_v_1034_);
lean_inc_ref(v_post_1019_);
lean_inc_ref(v_pre_1018_);
v___x_1035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1018_, v_post_1019_, v_usedLetOnly_1020_, v_skipConstInApp_1021_, v_skipInstances_1022_, v_v_1034_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v_bs_x27_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = lean_unsigned_to_nat(0u);
v_bs_x27_1038_ = lean_array_uset(v_bs_1025_, v_i_1024_, v___x_1037_);
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_add(v_i_1024_, v___x_1039_);
v___x_1041_ = lean_array_uset(v_bs_x27_1038_, v_i_1024_, v_a_1036_);
v_i_1024_ = v___x_1040_;
v_bs_1025_ = v___x_1041_;
goto _start;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_bs_1025_);
lean_dec_ref(v_post_1019_);
lean_dec_ref(v_pre_1018_);
v_a_1043_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1035_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1035_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1051_, lean_object* v_post_1052_, uint8_t v_usedLetOnly_1053_, uint8_t v_skipConstInApp_1054_, uint8_t v_skipInstances_1055_, lean_object* v___x_1056_, lean_object* v___y_1057_, lean_object* v_b_1058_, lean_object* v_a_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1051_, v_post_1052_, v_usedLetOnly_1053_, v_skipConstInApp_1054_, v_skipInstances_1055_, v___x_1056_, v___y_1057_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1075_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1070_ = lean_array_fset(v_b_1058_, v_a_1059_, v_a_1066_);
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1071_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_b_1058_);
v_a_1076_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1065_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1065_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1084_, lean_object* v_post_1085_, lean_object* v_usedLetOnly_1086_, lean_object* v_skipConstInApp_1087_, lean_object* v_skipInstances_1088_, lean_object* v___x_1089_, lean_object* v___y_1090_, lean_object* v_b_1091_, lean_object* v_a_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_usedLetOnly_boxed_1098_; uint8_t v_skipConstInApp_boxed_1099_; uint8_t v_skipInstances_boxed_1100_; lean_object* v_res_1101_; 
v_usedLetOnly_boxed_1098_ = lean_unbox(v_usedLetOnly_1086_);
v_skipConstInApp_boxed_1099_ = lean_unbox(v_skipConstInApp_1087_);
v_skipInstances_boxed_1100_ = lean_unbox(v_skipInstances_1088_);
v_res_1101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1084_, v_post_1085_, v_usedLetOnly_boxed_1098_, v_skipConstInApp_boxed_1099_, v_skipInstances_boxed_1100_, v___x_1089_, v___y_1090_, v_b_1091_, v_a_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v_a_1092_);
lean_dec(v___y_1090_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1102_, lean_object* v___x_1103_, lean_object* v_pre_1104_, lean_object* v_post_1105_, uint8_t v_usedLetOnly_1106_, uint8_t v_skipConstInApp_1107_, uint8_t v_skipInstances_1108_, lean_object* v_a_1109_, lean_object* v_b_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___y_1118_; uint8_t v___x_1141_; 
v___x_1141_ = lean_nat_dec_lt(v_a_1109_, v_upperBound_1102_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec(v_a_1109_);
lean_dec_ref(v_post_1105_);
lean_dec_ref(v_pre_1104_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_b_1110_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = lean_array_fget_borrowed(v_b_1110_, v_a_1109_);
v___x_1144_ = lean_array_get_size(v___x_1103_);
v___x_1145_ = lean_nat_dec_lt(v_a_1109_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___f_1149_; 
lean_inc(v___x_1143_);
v___x_1146_ = lean_box(v_usedLetOnly_1106_);
v___x_1147_ = lean_box(v_skipConstInApp_1107_);
v___x_1148_ = lean_box(v_skipInstances_1108_);
lean_inc(v_a_1109_);
lean_inc(v___y_1111_);
lean_inc_ref(v_post_1105_);
lean_inc_ref(v_pre_1104_);
v___f_1149_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1149_, 0, v_pre_1104_);
lean_closure_set(v___f_1149_, 1, v_post_1105_);
lean_closure_set(v___f_1149_, 2, v___x_1146_);
lean_closure_set(v___f_1149_, 3, v___x_1147_);
lean_closure_set(v___f_1149_, 4, v___x_1148_);
lean_closure_set(v___f_1149_, 5, v___x_1143_);
lean_closure_set(v___f_1149_, 6, v___y_1111_);
lean_closure_set(v___f_1149_, 7, v_b_1110_);
lean_closure_set(v___f_1149_, 8, v_a_1109_);
v___y_1118_ = v___f_1149_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1150_; uint8_t v_isInstance_1151_; 
v___x_1150_ = lean_array_fget_borrowed(v___x_1103_, v_a_1109_);
v_isInstance_1151_ = lean_ctor_get_uint8(v___x_1150_, sizeof(void*)*1 + 4);
if (v_isInstance_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___f_1155_; 
lean_inc(v___x_1143_);
v___x_1152_ = lean_box(v_usedLetOnly_1106_);
v___x_1153_ = lean_box(v_skipConstInApp_1107_);
v___x_1154_ = lean_box(v_skipInstances_1108_);
lean_inc(v_a_1109_);
lean_inc(v___y_1111_);
lean_inc_ref(v_post_1105_);
lean_inc_ref(v_pre_1104_);
v___f_1155_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1155_, 0, v_pre_1104_);
lean_closure_set(v___f_1155_, 1, v_post_1105_);
lean_closure_set(v___f_1155_, 2, v___x_1152_);
lean_closure_set(v___f_1155_, 3, v___x_1153_);
lean_closure_set(v___f_1155_, 4, v___x_1154_);
lean_closure_set(v___f_1155_, 5, v___x_1143_);
lean_closure_set(v___f_1155_, 6, v___y_1111_);
lean_closure_set(v___f_1155_, 7, v_b_1110_);
lean_closure_set(v___f_1155_, 8, v_a_1109_);
v___y_1118_ = v___f_1155_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1156_; lean_object* v___f_1157_; 
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1110_);
v___f_1157_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1157_, 0, v___x_1156_);
v___y_1118_ = v___f_1157_;
goto v___jp_1117_;
}
}
}
v___jp_1117_:
{
lean_object* v___x_1119_; 
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
v___x_1119_ = lean_apply_5(v___y_1118_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1132_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
if (lean_obj_tag(v_a_1120_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; 
lean_dec(v_a_1109_);
lean_dec_ref(v_post_1105_);
lean_dec_ref(v_pre_1104_);
v_a_1124_ = lean_ctor_get(v_a_1120_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v_a_1120_, 1);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_a_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_1122_);
v_a_1128_ = lean_ctor_get(v_a_1120_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v_a_1120_, 1);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_a_1109_, v___x_1129_);
lean_dec(v_a_1109_);
v_a_1109_ = v___x_1130_;
v_b_1110_ = v_a_1128_;
goto _start;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1109_);
lean_dec_ref(v_post_1105_);
lean_dec_ref(v_pre_1104_);
v_a_1133_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1119_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1119_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1158_, lean_object* v_pre_1159_, lean_object* v_post_1160_, uint8_t v_usedLetOnly_1161_, uint8_t v_skipConstInApp_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_f_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; 
if (lean_obj_tag(v_x_1163_) == 5)
{
lean_object* v_fn_1221_; lean_object* v_arg_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_fn_1221_ = lean_ctor_get(v_x_1163_, 0);
lean_inc_ref(v_fn_1221_);
v_arg_1222_ = lean_ctor_get(v_x_1163_, 1);
lean_inc_ref(v_arg_1222_);
lean_dec_ref_known(v_x_1163_, 2);
v___x_1223_ = lean_array_set(v_x_1164_, v_x_1165_, v_arg_1222_);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_sub(v_x_1165_, v___x_1224_);
lean_dec(v_x_1165_);
v_x_1163_ = v_fn_1221_;
v_x_1164_ = v___x_1223_;
v_x_1165_ = v___x_1225_;
goto _start;
}
else
{
lean_dec(v_x_1165_);
if (v_skipConstInApp_1162_ == 0)
{
goto v___jp_1218_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = l_Lean_Expr_isConst(v_x_1163_);
if (v___x_1227_ == 0)
{
goto v___jp_1218_;
}
else
{
v_f_1173_ = v_x_1163_;
v___y_1174_ = v___y_1166_;
v___y_1175_ = v___y_1167_;
v___y_1176_ = v___y_1168_;
v___y_1177_ = v___y_1169_;
v___y_1178_ = v___y_1170_;
goto v___jp_1172_;
}
}
}
v___jp_1172_:
{
if (v_skipInstances_1158_ == 0)
{
size_t v_sz_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v_sz_1179_ = lean_array_size(v_x_1164_);
v___x_1180_ = ((size_t)0ULL);
lean_inc_ref(v_post_1160_);
lean_inc_ref(v_pre_1159_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1158_, v_sz_1179_, v___x_1180_, v_x_1164_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l_Lean_mkAppN(v_f_1173_, v_a_1182_);
lean_dec(v_a_1182_);
v___x_1184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1158_, v___x_1183_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1184_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_f_1173_);
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
v_a_1185_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1181_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1181_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_array_get_size(v_x_1164_);
lean_inc_ref(v_f_1173_);
v___x_1194_ = l_Lean_Meta_getFunInfoNArgs(v_f_1173_, v___x_1193_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_paramInfo_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v_paramInfo_1196_ = lean_ctor_get(v_a_1195_, 0);
lean_inc_ref(v_paramInfo_1196_);
lean_dec(v_a_1195_);
v___x_1197_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1160_);
lean_inc_ref(v_pre_1159_);
v___x_1198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1193_, v_paramInfo_1196_, v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1158_, v___x_1197_, v_x_1164_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec_ref(v_paramInfo_1196_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = l_Lean_mkAppN(v_f_1173_, v_a_1199_);
lean_dec(v_a_1199_);
v___x_1201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1158_, v___x_1200_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1201_;
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_f_1173_);
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
v_a_1202_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1198_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1198_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_f_1173_);
lean_dec_ref(v_x_1164_);
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
v_a_1210_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1194_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1194_);
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
v___jp_1218_:
{
lean_object* v___x_1219_; 
lean_inc_ref(v_post_1160_);
lean_inc_ref(v_pre_1159_);
v___x_1219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1158_, v_x_1163_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v_f_1173_ = v_a_1220_;
v___y_1174_ = v___y_1166_;
v___y_1175_ = v___y_1167_;
v___y_1176_ = v___y_1168_;
v___y_1177_ = v___y_1169_;
v___y_1178_ = v___y_1170_;
goto v___jp_1172_;
}
else
{
lean_dec_ref(v_x_1164_);
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1228_, lean_object* v_pre_1229_, lean_object* v_e_1230_, lean_object* v_post_1231_, uint8_t v_usedLetOnly_1232_, uint8_t v_skipConstInApp_1233_, uint8_t v_skipInstances_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Core_checkSystem(v___x_1228_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; 
lean_dec_ref_known(v___x_1241_, 1);
lean_inc_ref(v_pre_1229_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc_ref(v_e_1230_);
v___x_1242_ = lean_apply_6(v_pre_1229_, v_e_1230_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, lean_box(0));
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1291_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1291_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1291_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___y_1248_; 
switch(lean_obj_tag(v_a_1243_))
{
case 0:
{
lean_object* v_e_1283_; lean_object* v___x_1285_; 
lean_dec_ref(v_post_1231_);
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_pre_1229_);
v_e_1283_ = lean_ctor_get(v_a_1243_, 0);
lean_inc_ref(v_e_1283_);
lean_dec_ref_known(v_a_1243_, 1);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_e_1283_);
v___x_1285_ = v___x_1245_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_e_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
case 1:
{
lean_object* v_e_1287_; lean_object* v___x_1288_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v_e_1230_);
v_e_1287_ = lean_ctor_get(v_a_1243_, 0);
lean_inc_ref(v_e_1287_);
lean_dec_ref_known(v_a_1243_, 1);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v_e_1287_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1288_;
}
default: 
{
lean_object* v_e_x3f_1289_; 
lean_del_object(v___x_1245_);
v_e_x3f_1289_ = lean_ctor_get(v_a_1243_, 0);
lean_inc(v_e_x3f_1289_);
lean_dec_ref_known(v_a_1243_, 1);
if (lean_obj_tag(v_e_x3f_1289_) == 0)
{
v___y_1248_ = v_e_1230_;
goto v___jp_1247_;
}
else
{
lean_object* v_val_1290_; 
lean_dec_ref(v_e_1230_);
v_val_1290_ = lean_ctor_get(v_e_x3f_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v_e_x3f_1289_, 1);
v___y_1248_ = v_val_1290_;
goto v___jp_1247_;
}
}
}
v___jp_1247_:
{
switch(lean_obj_tag(v___y_1248_))
{
case 7:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___x_1249_, v___y_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1250_;
}
case 6:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___x_1251_, v___y_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1252_;
}
case 8:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___x_1253_, v___y_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1254_;
}
case 5:
{
lean_object* v_dummy_1255_; lean_object* v_nargs_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_dummy_1255_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1256_ = l_Lean_Expr_getAppNumArgs(v___y_1248_);
lean_inc(v_nargs_1256_);
v___x_1257_ = lean_mk_array(v_nargs_1256_, v_dummy_1255_);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_sub(v_nargs_1256_, v___x_1258_);
lean_dec(v_nargs_1256_);
v___x_1260_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1234_, v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v___y_1248_, v___x_1257_, v___x_1259_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1260_;
}
case 10:
{
lean_object* v_data_1261_; lean_object* v_expr_1262_; lean_object* v___x_1263_; 
v_data_1261_ = lean_ctor_get(v___y_1248_, 0);
v_expr_1262_ = lean_ctor_get(v___y_1248_, 1);
lean_inc_ref(v_expr_1262_);
lean_inc_ref(v_post_1231_);
lean_inc_ref(v_pre_1229_);
v___x_1263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v_expr_1262_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = lean_ptr_addr(v_expr_1262_);
v___x_1266_ = lean_ptr_addr(v_a_1264_);
v___x_1267_ = lean_usize_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_inc(v_data_1261_);
lean_dec_ref_known(v___y_1248_, 2);
v___x_1268_ = l_Lean_Expr_mdata___override(v_data_1261_, v_a_1264_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___x_1268_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_a_1264_);
v___x_1270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___y_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1270_;
}
}
else
{
lean_dec_ref_known(v___y_1248_, 2);
lean_dec_ref(v_post_1231_);
lean_dec_ref(v_pre_1229_);
return v___x_1263_;
}
}
case 11:
{
lean_object* v_typeName_1271_; lean_object* v_idx_1272_; lean_object* v_struct_1273_; lean_object* v___x_1274_; 
v_typeName_1271_ = lean_ctor_get(v___y_1248_, 0);
v_idx_1272_ = lean_ctor_get(v___y_1248_, 1);
v_struct_1273_ = lean_ctor_get(v___y_1248_, 2);
lean_inc_ref(v_struct_1273_);
lean_inc_ref(v_post_1231_);
lean_inc_ref(v_pre_1229_);
v___x_1274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v_struct_1273_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; size_t v___x_1276_; size_t v___x_1277_; uint8_t v___x_1278_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_ptr_addr(v_struct_1273_);
v___x_1277_ = lean_ptr_addr(v_a_1275_);
v___x_1278_ = lean_usize_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_inc(v_idx_1272_);
lean_inc(v_typeName_1271_);
lean_dec_ref_known(v___y_1248_, 3);
v___x_1279_ = l_Lean_Expr_proj___override(v_typeName_1271_, v_idx_1272_, v_a_1275_);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___x_1279_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_a_1275_);
v___x_1281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___y_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1281_;
}
}
else
{
lean_dec_ref_known(v___y_1248_, 3);
lean_dec_ref(v_post_1231_);
lean_dec_ref(v_pre_1229_);
return v___x_1274_;
}
}
default: 
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1229_, v_post_1231_, v_usedLetOnly_1232_, v_skipConstInApp_1233_, v_skipInstances_1234_, v___y_1248_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_post_1231_);
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_pre_1229_);
v_a_1292_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1242_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1242_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_post_1231_);
lean_dec_ref(v_e_1230_);
lean_dec_ref(v_pre_1229_);
v_a_1300_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1241_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1241_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1308_, lean_object* v_pre_1309_, lean_object* v_e_1310_, lean_object* v_post_1311_, lean_object* v_usedLetOnly_1312_, lean_object* v_skipConstInApp_1313_, lean_object* v_skipInstances_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v_usedLetOnly_boxed_1321_; uint8_t v_skipConstInApp_boxed_1322_; uint8_t v_skipInstances_boxed_1323_; lean_object* v_res_1324_; 
v_usedLetOnly_boxed_1321_ = lean_unbox(v_usedLetOnly_1312_);
v_skipConstInApp_boxed_1322_ = lean_unbox(v_skipConstInApp_1313_);
v_skipInstances_boxed_1323_ = lean_unbox(v_skipInstances_1314_);
v_res_1324_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1308_, v_pre_1309_, v_e_1310_, v_post_1311_, v_usedLetOnly_boxed_1321_, v_skipConstInApp_boxed_1322_, v_skipInstances_boxed_1323_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1325_, lean_object* v_post_1326_, uint8_t v_usedLetOnly_1327_, uint8_t v_skipConstInApp_1328_, uint8_t v_skipInstances_1329_, lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_inc(v_a_1331_);
v___x_1337_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1337_, 0, lean_box(0));
lean_closure_set(v___x_1337_, 1, lean_box(0));
lean_closure_set(v___x_1337_, 2, v_a_1331_);
v___x_1338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1337_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1373_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1373_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1373_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1339_, v_e_1330_);
lean_dec(v_a_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___f_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1341_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1345_ = lean_box(v_usedLetOnly_1327_);
v___x_1346_ = lean_box(v_skipConstInApp_1328_);
v___x_1347_ = lean_box(v_skipInstances_1329_);
lean_inc_ref(v_e_1330_);
v___f_1348_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1348_, 0, v___x_1344_);
lean_closure_set(v___f_1348_, 1, v_pre_1325_);
lean_closure_set(v___f_1348_, 2, v_e_1330_);
lean_closure_set(v___f_1348_, 3, v_post_1326_);
lean_closure_set(v___f_1348_, 4, v___x_1345_);
lean_closure_set(v___f_1348_, 5, v___x_1346_);
lean_closure_set(v___f_1348_, 6, v___x_1347_);
v___x_1349_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1348_, v_a_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_a_1350_, 2);
lean_dec_ref_known(v___x_1349_, 1);
lean_inc(v_a_1331_);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1351_, 0, v_a_1331_);
lean_closure_set(v___f_1351_, 1, v_e_1330_);
lean_closure_set(v___f_1351_, 2, v_a_1350_);
v___x_1352_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1351_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1360_);
v___x_1354_ = v___x_1352_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_a_1350_);
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1350_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1350_);
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1352_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1352_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_dec_ref(v_e_1330_);
return v___x_1349_;
}
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; 
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_post_1326_);
lean_dec_ref(v_pre_1325_);
v_val_1369_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1343_, 1);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_val_1369_);
v___x_1371_ = v___x_1341_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_val_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_post_1326_);
lean_dec_ref(v_pre_1325_);
v_a_1374_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1338_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1338_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1382_, lean_object* v_pre_1383_, lean_object* v_post_1384_, lean_object* v_usedLetOnly_1385_, lean_object* v_skipConstInApp_1386_, lean_object* v_skipInstances_1387_, lean_object* v_body_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v_usedLetOnly_boxed_1396_; uint8_t v_skipConstInApp_boxed_1397_; uint8_t v_skipInstances_boxed_1398_; lean_object* v_res_1399_; 
v_usedLetOnly_boxed_1396_ = lean_unbox(v_usedLetOnly_1385_);
v_skipConstInApp_boxed_1397_ = lean_unbox(v_skipConstInApp_1386_);
v_skipInstances_boxed_1398_ = lean_unbox(v_skipInstances_1387_);
v_res_1399_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1382_, v_pre_1383_, v_post_1384_, v_usedLetOnly_boxed_1396_, v_skipConstInApp_boxed_1397_, v_skipInstances_boxed_1398_, v_body_1388_, v_x_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1400_, lean_object* v_post_1401_, uint8_t v_usedLetOnly_1402_, uint8_t v_skipConstInApp_1403_, uint8_t v_skipInstances_1404_, lean_object* v_fvars_1405_, lean_object* v_e_1406_, lean_object* v_a_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
if (lean_obj_tag(v_e_1406_) == 7)
{
lean_object* v_binderName_1413_; lean_object* v_binderType_1414_; lean_object* v_body_1415_; uint8_t v_binderInfo_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_binderName_1413_ = lean_ctor_get(v_e_1406_, 0);
lean_inc(v_binderName_1413_);
v_binderType_1414_ = lean_ctor_get(v_e_1406_, 1);
lean_inc_ref(v_binderType_1414_);
v_body_1415_ = lean_ctor_get(v_e_1406_, 2);
lean_inc_ref(v_body_1415_);
v_binderInfo_1416_ = lean_ctor_get_uint8(v_e_1406_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1406_, 3);
v___x_1417_ = lean_expr_instantiate_rev(v_binderType_1414_, v_fvars_1405_);
lean_dec_ref(v_binderType_1414_);
lean_inc_ref(v_post_1401_);
lean_inc_ref(v_pre_1400_);
v___x_1418_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1400_, v_post_1401_, v_usedLetOnly_1402_, v_skipConstInApp_1403_, v_skipInstances_1404_, v___x_1417_, v_a_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___f_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_box(v_usedLetOnly_1402_);
v___x_1421_ = lean_box(v_skipConstInApp_1403_);
v___x_1422_ = lean_box(v_skipInstances_1404_);
v___f_1423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1423_, 0, v_fvars_1405_);
lean_closure_set(v___f_1423_, 1, v_pre_1400_);
lean_closure_set(v___f_1423_, 2, v_post_1401_);
lean_closure_set(v___f_1423_, 3, v___x_1420_);
lean_closure_set(v___f_1423_, 4, v___x_1421_);
lean_closure_set(v___f_1423_, 5, v___x_1422_);
lean_closure_set(v___f_1423_, 6, v_body_1415_);
v___x_1424_ = 0;
v___x_1425_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1413_, v_binderInfo_1416_, v_a_1419_, v___f_1423_, v___x_1424_, v_a_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1425_;
}
else
{
lean_dec_ref(v_body_1415_);
lean_dec(v_binderName_1413_);
lean_dec_ref(v_fvars_1405_);
lean_dec_ref(v_post_1401_);
lean_dec_ref(v_pre_1400_);
return v___x_1418_;
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_expr_instantiate_rev(v_e_1406_, v_fvars_1405_);
lean_dec_ref(v_e_1406_);
lean_inc_ref(v_post_1401_);
lean_inc_ref(v_pre_1400_);
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1400_, v_post_1401_, v_usedLetOnly_1402_, v_skipConstInApp_1403_, v_skipInstances_1404_, v___x_1426_, v_a_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; uint8_t v___x_1429_; uint8_t v___x_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1429_ = 0;
v___x_1430_ = 1;
v___x_1431_ = 1;
v___x_1432_ = l_Lean_Meta_mkForallFVars(v_fvars_1405_, v_a_1428_, v___x_1429_, v_usedLetOnly_1402_, v___x_1430_, v___x_1431_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec_ref(v_fvars_1405_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1400_, v_post_1401_, v_usedLetOnly_1402_, v_skipConstInApp_1403_, v_skipInstances_1404_, v_a_1433_, v_a_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1434_;
}
else
{
lean_dec_ref(v_post_1401_);
lean_dec_ref(v_pre_1400_);
return v___x_1432_;
}
}
else
{
lean_dec_ref(v_fvars_1405_);
lean_dec_ref(v_post_1401_);
lean_dec_ref(v_pre_1400_);
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1435_, lean_object* v_pre_1436_, lean_object* v_post_1437_, uint8_t v_usedLetOnly_1438_, uint8_t v_skipConstInApp_1439_, uint8_t v_skipInstances_1440_, lean_object* v_body_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_array_push(v_fvars_1435_, v_x_1442_);
v___x_1450_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1436_, v_post_1437_, v_usedLetOnly_1438_, v_skipConstInApp_1439_, v_skipInstances_1440_, v___x_1449_, v_body_1441_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1451_, lean_object* v_post_1452_, lean_object* v_usedLetOnly_1453_, lean_object* v_skipConstInApp_1454_, lean_object* v_skipInstances_1455_, lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_usedLetOnly_boxed_1463_; uint8_t v_skipConstInApp_boxed_1464_; uint8_t v_skipInstances_boxed_1465_; lean_object* v_res_1466_; 
v_usedLetOnly_boxed_1463_ = lean_unbox(v_usedLetOnly_1453_);
v_skipConstInApp_boxed_1464_ = lean_unbox(v_skipConstInApp_1454_);
v_skipInstances_boxed_1465_ = lean_unbox(v_skipInstances_1455_);
v_res_1466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1451_, v_post_1452_, v_usedLetOnly_boxed_1463_, v_skipConstInApp_boxed_1464_, v_skipInstances_boxed_1465_, v_e_1456_, v_a_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_a_1457_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1467_, lean_object* v_post_1468_, lean_object* v_usedLetOnly_1469_, lean_object* v_skipConstInApp_1470_, lean_object* v_skipInstances_1471_, lean_object* v_sz_1472_, lean_object* v_i_1473_, lean_object* v_bs_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
uint8_t v_usedLetOnly_boxed_1481_; uint8_t v_skipConstInApp_boxed_1482_; uint8_t v_skipInstances_boxed_1483_; size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_usedLetOnly_boxed_1481_ = lean_unbox(v_usedLetOnly_1469_);
v_skipConstInApp_boxed_1482_ = lean_unbox(v_skipConstInApp_1470_);
v_skipInstances_boxed_1483_ = lean_unbox(v_skipInstances_1471_);
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1472_);
lean_dec(v_sz_1472_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1467_, v_post_1468_, v_usedLetOnly_boxed_1481_, v_skipConstInApp_boxed_1482_, v_skipInstances_boxed_1483_, v_sz_boxed_1484_, v_i_boxed_1485_, v_bs_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1487_, lean_object* v_post_1488_, lean_object* v_usedLetOnly_1489_, lean_object* v_skipConstInApp_1490_, lean_object* v_skipInstances_1491_, lean_object* v_e_1492_, lean_object* v_a_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_usedLetOnly_boxed_1499_; uint8_t v_skipConstInApp_boxed_1500_; uint8_t v_skipInstances_boxed_1501_; lean_object* v_res_1502_; 
v_usedLetOnly_boxed_1499_ = lean_unbox(v_usedLetOnly_1489_);
v_skipConstInApp_boxed_1500_ = lean_unbox(v_skipConstInApp_1490_);
v_skipInstances_boxed_1501_ = lean_unbox(v_skipInstances_1491_);
v_res_1502_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1487_, v_post_1488_, v_usedLetOnly_boxed_1499_, v_skipConstInApp_boxed_1500_, v_skipInstances_boxed_1501_, v_e_1492_, v_a_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v_a_1493_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1503_, lean_object* v_post_1504_, lean_object* v_usedLetOnly_1505_, lean_object* v_skipConstInApp_1506_, lean_object* v_skipInstances_1507_, lean_object* v_fvars_1508_, lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v_usedLetOnly_boxed_1516_; uint8_t v_skipConstInApp_boxed_1517_; uint8_t v_skipInstances_boxed_1518_; lean_object* v_res_1519_; 
v_usedLetOnly_boxed_1516_ = lean_unbox(v_usedLetOnly_1505_);
v_skipConstInApp_boxed_1517_ = lean_unbox(v_skipConstInApp_1506_);
v_skipInstances_boxed_1518_ = lean_unbox(v_skipInstances_1507_);
v_res_1519_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1503_, v_post_1504_, v_usedLetOnly_boxed_1516_, v_skipConstInApp_boxed_1517_, v_skipInstances_boxed_1518_, v_fvars_1508_, v_e_1509_, v_a_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_a_1510_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1520_, lean_object* v_post_1521_, lean_object* v_usedLetOnly_1522_, lean_object* v_skipConstInApp_1523_, lean_object* v_skipInstances_1524_, lean_object* v_fvars_1525_, lean_object* v_e_1526_, lean_object* v_a_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_usedLetOnly_boxed_1533_; uint8_t v_skipConstInApp_boxed_1534_; uint8_t v_skipInstances_boxed_1535_; lean_object* v_res_1536_; 
v_usedLetOnly_boxed_1533_ = lean_unbox(v_usedLetOnly_1522_);
v_skipConstInApp_boxed_1534_ = lean_unbox(v_skipConstInApp_1523_);
v_skipInstances_boxed_1535_ = lean_unbox(v_skipInstances_1524_);
v_res_1536_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1520_, v_post_1521_, v_usedLetOnly_boxed_1533_, v_skipConstInApp_boxed_1534_, v_skipInstances_boxed_1535_, v_fvars_1525_, v_e_1526_, v_a_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v_a_1527_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1537_, lean_object* v_post_1538_, lean_object* v_usedLetOnly_1539_, lean_object* v_skipConstInApp_1540_, lean_object* v_skipInstances_1541_, lean_object* v_fvars_1542_, lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v_usedLetOnly_boxed_1550_; uint8_t v_skipConstInApp_boxed_1551_; uint8_t v_skipInstances_boxed_1552_; lean_object* v_res_1553_; 
v_usedLetOnly_boxed_1550_ = lean_unbox(v_usedLetOnly_1539_);
v_skipConstInApp_boxed_1551_ = lean_unbox(v_skipConstInApp_1540_);
v_skipInstances_boxed_1552_ = lean_unbox(v_skipInstances_1541_);
v_res_1553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1537_, v_post_1538_, v_usedLetOnly_boxed_1550_, v_skipConstInApp_boxed_1551_, v_skipInstances_boxed_1552_, v_fvars_1542_, v_e_1543_, v_a_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v_a_1544_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1554_, lean_object* v___x_1555_, lean_object* v_pre_1556_, lean_object* v_post_1557_, lean_object* v_usedLetOnly_1558_, lean_object* v_skipConstInApp_1559_, lean_object* v_skipInstances_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_usedLetOnly_boxed_1569_; uint8_t v_skipConstInApp_boxed_1570_; uint8_t v_skipInstances_boxed_1571_; lean_object* v_res_1572_; 
v_usedLetOnly_boxed_1569_ = lean_unbox(v_usedLetOnly_1558_);
v_skipConstInApp_boxed_1570_ = lean_unbox(v_skipConstInApp_1559_);
v_skipInstances_boxed_1571_ = lean_unbox(v_skipInstances_1560_);
v_res_1572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1554_, v___x_1555_, v_pre_1556_, v_post_1557_, v_usedLetOnly_boxed_1569_, v_skipConstInApp_boxed_1570_, v_skipInstances_boxed_1571_, v_a_1561_, v_b_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___x_1555_);
lean_dec(v_upperBound_1554_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1573_, lean_object* v_pre_1574_, lean_object* v_post_1575_, lean_object* v_usedLetOnly_1576_, lean_object* v_skipConstInApp_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_skipInstances_boxed_1587_; uint8_t v_usedLetOnly_boxed_1588_; uint8_t v_skipConstInApp_boxed_1589_; lean_object* v_res_1590_; 
v_skipInstances_boxed_1587_ = lean_unbox(v_skipInstances_1573_);
v_usedLetOnly_boxed_1588_ = lean_unbox(v_usedLetOnly_1576_);
v_skipConstInApp_boxed_1589_ = lean_unbox(v_skipConstInApp_1577_);
v_res_1590_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1587_, v_pre_1574_, v_post_1575_, v_usedLetOnly_boxed_1588_, v_skipConstInApp_boxed_1589_, v_x_1578_, v_x_1579_, v_x_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_unsigned_to_nat(16u);
v___x_1593_ = lean_mk_array(v___x_1592_, v___x_1591_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1598_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1598_, 0, lean_box(0));
lean_closure_set(v___x_1598_, 1, lean_box(0));
lean_closure_set(v___x_1598_, 2, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1599_, lean_object* v_pre_1600_, lean_object* v_post_1601_, uint8_t v_usedLetOnly_1602_, uint8_t v_skipConstInApp_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_a_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; 
v___x_1609_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1610_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1609_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = 0;
v___x_1613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1600_, v_post_1601_, v_usedLetOnly_1602_, v_skipConstInApp_1603_, v___x_1612_, v_input_1599_, v_a_1611_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1615_, 0, lean_box(0));
lean_closure_set(v___x_1615_, 1, lean_box(0));
lean_closure_set(v___x_1615_, 2, v_a_1611_);
v___x_1616_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1615_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1624_);
v___x_1618_ = v___x_1616_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___x_1616_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_a_1614_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1614_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_dec(v_a_1611_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1625_, lean_object* v_pre_1626_, lean_object* v_post_1627_, lean_object* v_usedLetOnly_1628_, lean_object* v_skipConstInApp_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v_usedLetOnly_boxed_1635_; uint8_t v_skipConstInApp_boxed_1636_; lean_object* v_res_1637_; 
v_usedLetOnly_boxed_1635_ = lean_unbox(v_usedLetOnly_1628_);
v_skipConstInApp_boxed_1636_ = lean_unbox(v_skipConstInApp_1629_);
v_res_1637_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1625_, v_pre_1626_, v_post_1627_, v_usedLetOnly_boxed_1635_, v_skipConstInApp_boxed_1636_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1637_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__1(void){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Array_instInhabited(lean_box(0));
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__3(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__2));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__5(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__4));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1646_, lean_object* v_argsPacker_1647_, lean_object* v_funNames_1648_, lean_object* v_newF_1649_, lean_object* v_e_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; 
lean_inc(v_a_1654_);
lean_inc_ref(v_a_1653_);
lean_inc(v_a_1652_);
lean_inc_ref(v_a_1651_);
lean_inc_ref(v_newF_1649_);
v___x_1656_ = lean_infer_type(v_newF_1649_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___x_1670_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___f_1658_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1659_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_1670_ = l_Lean_Expr_isForall(v_a_1657_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_e_1650_);
lean_dec_ref(v_funNames_1648_);
lean_dec_ref(v_argsPacker_1647_);
lean_dec_ref(v_fixedParamPerms_1646_);
v___x_1671_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__3, &l_Lean_Elab_WF_packCalls___closed__3_once, _init_l_Lean_Elab_WF_packCalls___closed__3);
v___x_1672_ = l_Lean_MessageData_ofExpr(v_newF_1649_);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__5, &l_Lean_Elab_WF_packCalls___closed__5_once, _init_l_Lean_Elab_WF_packCalls___closed__5);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_MessageData_ofExpr(v_a_1657_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1677_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
v___y_1661_ = v_a_1651_;
v___y_1662_ = v_a_1652_;
v___y_1663_ = v_a_1653_;
v___y_1664_ = v_a_1654_;
goto v___jp_1660_;
}
v___jp_1660_:
{
lean_object* v___x_1665_; lean_object* v___f_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1665_ = l_Lean_Expr_bindingDomain_x21(v_a_1657_);
lean_dec(v_a_1657_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 12, 6);
lean_closure_set(v___f_1666_, 0, v_funNames_1648_);
lean_closure_set(v___f_1666_, 1, v_fixedParamPerms_1646_);
lean_closure_set(v___f_1666_, 2, v___x_1659_);
lean_closure_set(v___f_1666_, 3, v_argsPacker_1647_);
lean_closure_set(v___f_1666_, 4, v___x_1665_);
lean_closure_set(v___f_1666_, 5, v_newF_1649_);
v___x_1667_ = 0;
v___x_1668_ = 1;
v___x_1669_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1650_, v___f_1658_, v___f_1666_, v___x_1667_, v___x_1668_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1669_;
}
}
else
{
lean_dec_ref(v_e_1650_);
lean_dec_ref(v_newF_1649_);
lean_dec_ref(v_funNames_1648_);
lean_dec_ref(v_argsPacker_1647_);
lean_dec_ref(v_fixedParamPerms_1646_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1687_, lean_object* v_argsPacker_1688_, lean_object* v_funNames_1689_, lean_object* v_newF_1690_, lean_object* v_e_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1687_, v_argsPacker_1688_, v_funNames_1689_, v_newF_1690_, v_e_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1698_, lean_object* v___x_1699_, lean_object* v_pre_1700_, lean_object* v_post_1701_, uint8_t v_usedLetOnly_1702_, uint8_t v_skipConstInApp_1703_, uint8_t v_skipInstances_1704_, lean_object* v___x_1705_, lean_object* v_inst_1706_, lean_object* v_R_1707_, lean_object* v_a_1708_, lean_object* v_b_1709_, lean_object* v_c_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1698_, v___x_1699_, v_pre_1700_, v_post_1701_, v_usedLetOnly_1702_, v_skipConstInApp_1703_, v_skipInstances_1704_, v_a_1708_, v_b_1709_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1718_ = _args[0];
lean_object* v___x_1719_ = _args[1];
lean_object* v_pre_1720_ = _args[2];
lean_object* v_post_1721_ = _args[3];
lean_object* v_usedLetOnly_1722_ = _args[4];
lean_object* v_skipConstInApp_1723_ = _args[5];
lean_object* v_skipInstances_1724_ = _args[6];
lean_object* v___x_1725_ = _args[7];
lean_object* v_inst_1726_ = _args[8];
lean_object* v_R_1727_ = _args[9];
lean_object* v_a_1728_ = _args[10];
lean_object* v_b_1729_ = _args[11];
lean_object* v_c_1730_ = _args[12];
lean_object* v___y_1731_ = _args[13];
lean_object* v___y_1732_ = _args[14];
lean_object* v___y_1733_ = _args[15];
lean_object* v___y_1734_ = _args[16];
lean_object* v___y_1735_ = _args[17];
lean_object* v___y_1736_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1737_; uint8_t v_skipConstInApp_boxed_1738_; uint8_t v_skipInstances_boxed_1739_; lean_object* v_res_1740_; 
v_usedLetOnly_boxed_1737_ = lean_unbox(v_usedLetOnly_1722_);
v_skipConstInApp_boxed_1738_ = lean_unbox(v_skipConstInApp_1723_);
v_skipInstances_boxed_1739_ = lean_unbox(v_skipInstances_1724_);
v_res_1740_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1718_, v___x_1719_, v_pre_1720_, v_post_1721_, v_usedLetOnly_boxed_1737_, v_skipConstInApp_boxed_1738_, v_skipInstances_boxed_1739_, v___x_1725_, v_inst_1726_, v_R_1727_, v_a_1728_, v_b_1729_, v_c_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec(v___x_1725_);
lean_dec_ref(v___x_1719_);
lean_dec(v_upperBound_1718_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1741_, lean_object* v_m_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1742_, v_a_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1745_, lean_object* v_m_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1745_, v_m_1746_, v_a_1747_);
lean_dec_ref(v_a_1747_);
lean_dec_ref(v_m_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1749_, lean_object* v_name_1750_, uint8_t v_bi_1751_, lean_object* v_type_1752_, lean_object* v_k_1753_, uint8_t v_kind_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1750_, v_bi_1751_, v_type_1752_, v_k_1753_, v_kind_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_name_1763_, lean_object* v_bi_1764_, lean_object* v_type_1765_, lean_object* v_k_1766_, lean_object* v_kind_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
uint8_t v_bi_boxed_1774_; uint8_t v_kind_boxed_1775_; lean_object* v_res_1776_; 
v_bi_boxed_1774_ = lean_unbox(v_bi_1764_);
v_kind_boxed_1775_ = lean_unbox(v_kind_1767_);
v_res_1776_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1762_, v_name_1763_, v_bi_boxed_1774_, v_type_1765_, v_k_1766_, v_kind_boxed_1775_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1777_, lean_object* v_name_1778_, lean_object* v_type_1779_, lean_object* v_val_1780_, lean_object* v_k_1781_, uint8_t v_nondep_1782_, uint8_t v_kind_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1778_, v_type_1779_, v_val_1780_, v_k_1781_, v_nondep_1782_, v_kind_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1791_, lean_object* v_name_1792_, lean_object* v_type_1793_, lean_object* v_val_1794_, lean_object* v_k_1795_, lean_object* v_nondep_1796_, lean_object* v_kind_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v_nondep_boxed_1804_; uint8_t v_kind_boxed_1805_; lean_object* v_res_1806_; 
v_nondep_boxed_1804_ = lean_unbox(v_nondep_1796_);
v_kind_boxed_1805_ = lean_unbox(v_kind_1797_);
v_res_1806_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1791_, v_name_1792_, v_type_1793_, v_val_1794_, v_k_1795_, v_nondep_boxed_1804_, v_kind_boxed_1805_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1807_, lean_object* v_ref_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1808_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_ref_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1815_, v_ref_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1823_, lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1832_, v_x_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1841_, lean_object* v_m_1842_, lean_object* v_a_1843_, lean_object* v_b_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1842_, v_a_1843_, v_b_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1846_, lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1847_, v_x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1850_, lean_object* v_a_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1850_, v_a_1851_, v_x_1852_);
lean_dec(v_x_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1854_, lean_object* v_a_1855_, lean_object* v_x_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1858_, lean_object* v_a_1859_, lean_object* v_x_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1858_, v_a_1859_, v_x_1860_);
lean_dec(v_x_1860_);
lean_dec_ref(v_a_1859_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1863_, lean_object* v_data_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1866_, lean_object* v_a_1867_, lean_object* v_b_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1867_, v_b_1868_, v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1871_, lean_object* v_i_1872_, lean_object* v_source_1873_, lean_object* v_target_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1872_, v_source_1873_, v_target_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1877_, v_x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1886_, lean_object* v_argsPacker_1887_, lean_object* v_preDefs_1888_){
_start:
{
lean_object* v___x_1889_; uint8_t v___y_1891_; uint8_t v___x_1908_; 
v___x_1889_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1908_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1886_);
if (v___x_1908_ == 0)
{
v___y_1891_ = v___x_1908_;
goto v___jp_1890_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1887_);
v___y_1891_ = v___x_1909_;
goto v___jp_1890_;
}
v___jp_1890_:
{
if (v___y_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1887_);
v___x_1894_ = lean_nat_dec_lt(v___x_1892_, v___x_1893_);
lean_dec(v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_declName_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_array_get_borrowed(v___x_1889_, v_preDefs_1888_, v___x_1895_);
v_declName_1897_ = lean_ctor_get(v___x_1896_, 3);
v___x_1898_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1897_);
v___x_1899_ = l_Lean_Name_append(v_declName_1897_, v___x_1898_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_declName_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_array_get_borrowed(v___x_1889_, v_preDefs_1888_, v___x_1900_);
v_declName_1902_ = lean_ctor_get(v___x_1901_, 3);
v___x_1903_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1902_);
v___x_1904_ = l_Lean_Name_append(v_declName_1902_, v___x_1903_);
return v___x_1904_;
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_declName_1907_; 
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_array_get_borrowed(v___x_1889_, v_preDefs_1888_, v___x_1905_);
v_declName_1907_ = lean_ctor_get(v___x_1906_, 3);
lean_inc(v_declName_1907_);
return v_declName_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1910_, lean_object* v_argsPacker_1911_, lean_object* v_preDefs_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1910_, v_argsPacker_1911_, v_preDefs_1912_);
lean_dec_ref(v_preDefs_1912_);
lean_dec_ref(v_argsPacker_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1914_, lean_object* v_b_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
lean_inc(v___y_1919_);
lean_inc_ref(v___y_1918_);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
v___x_1921_ = lean_apply_6(v_k_1914_, v_b_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, lean_box(0));
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1922_, v_b_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1930_, lean_object* v_type_1931_, lean_object* v_k_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___f_1938_; lean_object* v___x_1939_; 
v___f_1938_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1938_, 0, v_k_1932_);
v___x_1939_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1930_, v_type_1931_, v___f_1938_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1939_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1939_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1956_, lean_object* v_type_1957_, lean_object* v_k_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1956_, v_type_1957_, v_k_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1965_, lean_object* v_perm_1966_, lean_object* v_type_1967_, lean_object* v_k_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1966_, v_type_1967_, v_k_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_perm_1976_, lean_object* v_type_1977_, lean_object* v_k_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1975_, v_perm_1976_, v_type_1977_, v_k_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1985_, lean_object* v_ys_1986_, size_t v_sz_1987_, size_t v_i_1988_, lean_object* v_bs_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1988_, v_sz_1987_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec_ref(v_ys_1986_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_bs_1989_);
return v___x_1996_;
}
else
{
lean_object* v_v_1997_; lean_object* v_value_1998_; lean_object* v___x_1999_; lean_object* v_bs_x27_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_v_1997_ = lean_array_uget_borrowed(v_bs_1989_, v_i_1988_);
v_value_1998_ = lean_ctor_get(v_v_1997_, 7);
lean_inc_ref(v_value_1998_);
v___x_1999_ = lean_unsigned_to_nat(0u);
v_bs_x27_2000_ = lean_array_uset(v_bs_1989_, v_i_1988_, v___x_1999_);
v___x_2001_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2002_ = lean_usize_to_nat(v_i_1988_);
v___x_2003_ = lean_array_get_borrowed(v___x_2001_, v___x_1985_, v___x_2002_);
lean_dec(v___x_2002_);
lean_inc_ref(v_ys_1986_);
lean_inc(v___x_2003_);
v___x_2004_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2003_, v_value_1998_, v_ys_1986_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; size_t v___x_2006_; size_t v___x_2007_; lean_object* v___x_2008_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = ((size_t)1ULL);
v___x_2007_ = lean_usize_add(v_i_1988_, v___x_2006_);
v___x_2008_ = lean_array_uset(v_bs_x27_2000_, v_i_1988_, v_a_2005_);
v_i_1988_ = v___x_2007_;
v_bs_1989_ = v___x_2008_;
goto _start;
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec_ref(v_bs_x27_2000_);
lean_dec_ref(v_ys_1986_);
v_a_2010_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2004_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2004_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2018_, lean_object* v_ys_2019_, lean_object* v_sz_2020_, lean_object* v_i_2021_, lean_object* v_bs_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
size_t v_sz_boxed_2028_; size_t v_i_boxed_2029_; lean_object* v_res_2030_; 
v_sz_boxed_2028_ = lean_unbox_usize(v_sz_2020_);
lean_dec(v_sz_2020_);
v_i_boxed_2029_ = lean_unbox_usize(v_i_2021_);
lean_dec(v_i_2021_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2018_, v_ys_2019_, v_sz_boxed_2028_, v_i_boxed_2029_, v_bs_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec_ref(v___x_2018_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2031_, lean_object* v_ys_2032_, size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_bs_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_lt(v_i_2034_, v_sz_2033_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec_ref(v_ys_2032_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_bs_2035_);
return v___x_2042_;
}
else
{
lean_object* v_v_2043_; lean_object* v_type_2044_; lean_object* v___x_2045_; lean_object* v_bs_x27_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_v_2043_ = lean_array_uget_borrowed(v_bs_2035_, v_i_2034_);
v_type_2044_ = lean_ctor_get(v_v_2043_, 6);
lean_inc_ref(v_type_2044_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v_bs_x27_2046_ = lean_array_uset(v_bs_2035_, v_i_2034_, v___x_2045_);
v___x_2047_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2048_ = lean_usize_to_nat(v_i_2034_);
v___x_2049_ = lean_array_get_borrowed(v___x_2047_, v___x_2031_, v___x_2048_);
lean_dec(v___x_2048_);
lean_inc_ref(v_ys_2032_);
lean_inc(v___x_2049_);
v___x_2050_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2049_, v_type_2044_, v_ys_2032_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; size_t v___x_2052_; size_t v___x_2053_; lean_object* v___x_2054_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2034_, v___x_2052_);
v___x_2054_ = lean_array_uset(v_bs_x27_2046_, v_i_2034_, v_a_2051_);
v_i_2034_ = v___x_2053_;
v_bs_2035_ = v___x_2054_;
goto _start;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_bs_x27_2046_);
lean_dec_ref(v_ys_2032_);
v_a_2056_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2050_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2050_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2064_, lean_object* v_ys_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_bs_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2064_, v_ys_2065_, v_sz_boxed_2074_, v_i_boxed_2075_, v_bs_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec_ref(v___x_2064_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
if (lean_obj_tag(v_a_2077_) == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = l_List_reverse___redArg(v_a_2078_);
return v___x_2079_;
}
else
{
lean_object* v_head_2080_; lean_object* v_tail_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2090_; 
v_head_2080_ = lean_ctor_get(v_a_2077_, 0);
v_tail_2081_ = lean_ctor_get(v_a_2077_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2083_ = v_a_2077_;
v_isShared_2084_ = v_isSharedCheck_2090_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_tail_2081_);
lean_inc(v_head_2080_);
lean_dec(v_a_2077_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2090_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = l_Lean_mkLevelParam(v_head_2080_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v_a_2078_);
lean_ctor_set(v___x_2083_, 0, v___x_2085_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_a_2078_);
v___x_2087_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
v_a_2077_ = v_tail_2081_;
v_a_2078_ = v___x_2087_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_bs_2093_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2094_ == 0)
{
return v_bs_2093_;
}
else
{
lean_object* v_v_2095_; lean_object* v_declName_2096_; lean_object* v___x_2097_; lean_object* v_bs_x27_2098_; size_t v___x_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v_v_2095_ = lean_array_uget_borrowed(v_bs_2093_, v_i_2092_);
v_declName_2096_ = lean_ctor_get(v_v_2095_, 3);
lean_inc(v_declName_2096_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v_bs_x27_2098_ = lean_array_uset(v_bs_2093_, v_i_2092_, v___x_2097_);
v___x_2099_ = ((size_t)1ULL);
v___x_2100_ = lean_usize_add(v_i_2092_, v___x_2099_);
v___x_2101_ = lean_array_uset(v_bs_x27_2098_, v_i_2092_, v_declName_2096_);
v_i_2092_ = v___x_2100_;
v_bs_2093_ = v___x_2101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2103_, lean_object* v_i_2104_, lean_object* v_bs_2105_){
_start:
{
size_t v_sz_boxed_2106_; size_t v_i_boxed_2107_; lean_object* v_res_2108_; 
v_sz_boxed_2106_ = lean_unbox_usize(v_sz_2103_);
lean_dec(v_sz_2103_);
v_i_boxed_2107_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2106_, v_i_boxed_2107_, v_bs_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2109_, lean_object* v_perms_2110_, lean_object* v_argsPacker_2111_, uint8_t v___x_2112_, lean_object* v_ref_2113_, uint8_t v_kind_2114_, lean_object* v_levelParams_2115_, lean_object* v_modifiers_2116_, lean_object* v_newFn_2117_, lean_object* v_binders_2118_, lean_object* v_numSectionVars_2119_, lean_object* v_value_2120_, lean_object* v_termination_2121_, lean_object* v_fixedParamPerms_2122_, lean_object* v_ys_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
size_t v_sz_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
v_sz_2129_ = lean_array_size(v_preDefs_2109_);
v___x_2130_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2109_);
lean_inc_ref(v_ys_2123_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2110_, v_ys_2123_, v_sz_2129_, v___x_2130_, v_preDefs_2109_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
lean_inc_ref(v_preDefs_2109_);
lean_inc_ref(v_ys_2123_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2110_, v_ys_2123_, v_sz_2129_, v___x_2130_, v_preDefs_2109_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2135_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2111_, v_a_2132_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v_a_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = 1;
v___x_2138_ = 1;
v___x_2139_ = l_Lean_Meta_mkForallFVars(v_ys_2123_, v_a_2136_, v___x_2112_, v___x_2137_, v___x_2137_, v___x_2138_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc_n(v_a_2140_, 2);
lean_dec_ref_known(v___x_2139_, 1);
lean_inc_ref(v_termination_2121_);
lean_inc(v_numSectionVars_2119_);
lean_inc(v_binders_2118_);
lean_inc(v_newFn_2117_);
lean_inc_ref(v_modifiers_2116_);
lean_inc(v_levelParams_2115_);
lean_inc(v_ref_2113_);
v___x_2141_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2141_, 0, v_ref_2113_);
lean_ctor_set(v___x_2141_, 1, v_levelParams_2115_);
lean_ctor_set(v___x_2141_, 2, v_modifiers_2116_);
lean_ctor_set(v___x_2141_, 3, v_newFn_2117_);
lean_ctor_set(v___x_2141_, 4, v_binders_2118_);
lean_ctor_set(v___x_2141_, 5, v_numSectionVars_2119_);
lean_ctor_set(v___x_2141_, 6, v_a_2140_);
lean_ctor_set(v___x_2141_, 7, v_value_2120_);
lean_ctor_set(v___x_2141_, 8, v_termination_2121_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*9, v_kind_2114_);
v___x_2142_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2141_, v___y_2126_, v___y_2127_);
lean_dec_ref_known(v___x_2141_, 9);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; 
lean_dec_ref_known(v___x_2142_, 1);
v___x_2143_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2111_, v_a_2134_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v_a_2134_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = lean_box(0);
lean_inc(v_levelParams_2115_);
v___x_2146_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2115_, v___x_2145_);
lean_inc(v_newFn_2117_);
v___x_2147_ = l_Lean_mkConst(v_newFn_2117_, v___x_2146_);
v___x_2148_ = l_Lean_mkAppN(v___x_2147_, v_ys_2123_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2129_, v___x_2130_, v_preDefs_2109_);
v___x_2150_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2122_, v_argsPacker_2111_, v___x_2149_, v___x_2148_, v_a_2144_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l_Lean_Meta_mkLambdaFVars(v_ys_2123_, v_a_2151_, v___x_2112_, v___x_2137_, v___x_2112_, v___x_2137_, v___x_2138_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec_ref(v_ys_2123_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2157_, 0, v_ref_2113_);
lean_ctor_set(v___x_2157_, 1, v_levelParams_2115_);
lean_ctor_set(v___x_2157_, 2, v_modifiers_2116_);
lean_ctor_set(v___x_2157_, 3, v_newFn_2117_);
lean_ctor_set(v___x_2157_, 4, v_binders_2118_);
lean_ctor_set(v___x_2157_, 5, v_numSectionVars_2119_);
lean_ctor_set(v___x_2157_, 6, v_a_2140_);
lean_ctor_set(v___x_2157_, 7, v_a_2153_);
lean_ctor_set(v___x_2157_, 8, v_termination_2121_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*9, v_kind_2114_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2140_);
lean_dec_ref(v_termination_2121_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
v_a_2162_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2152_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2152_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2140_);
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_termination_2121_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
v_a_2170_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2150_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2150_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2140_);
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_fixedParamPerms_2122_);
lean_dec_ref(v_termination_2121_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
lean_dec_ref(v_argsPacker_2111_);
lean_dec_ref(v_preDefs_2109_);
v_a_2178_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2143_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2143_);
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
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2140_);
lean_dec(v_a_2134_);
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_fixedParamPerms_2122_);
lean_dec_ref(v_termination_2121_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
lean_dec_ref(v_argsPacker_2111_);
lean_dec_ref(v_preDefs_2109_);
v_a_2186_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2142_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2142_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_2134_);
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_fixedParamPerms_2122_);
lean_dec_ref(v_termination_2121_);
lean_dec_ref(v_value_2120_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
lean_dec_ref(v_argsPacker_2111_);
lean_dec_ref(v_preDefs_2109_);
v_a_2194_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2139_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2139_);
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
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_a_2134_);
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_fixedParamPerms_2122_);
lean_dec_ref(v_termination_2121_);
lean_dec_ref(v_value_2120_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
lean_dec_ref(v_argsPacker_2111_);
lean_dec_ref(v_preDefs_2109_);
v_a_2202_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2135_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2135_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_2132_);
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_fixedParamPerms_2122_);
lean_dec_ref(v_termination_2121_);
lean_dec_ref(v_value_2120_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
lean_dec_ref(v_argsPacker_2111_);
lean_dec_ref(v_preDefs_2109_);
v_a_2210_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2133_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2133_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_ys_2123_);
lean_dec_ref(v_fixedParamPerms_2122_);
lean_dec_ref(v_termination_2121_);
lean_dec_ref(v_value_2120_);
lean_dec(v_numSectionVars_2119_);
lean_dec(v_binders_2118_);
lean_dec(v_newFn_2117_);
lean_dec_ref(v_modifiers_2116_);
lean_dec(v_levelParams_2115_);
lean_dec(v_ref_2113_);
lean_dec_ref(v_argsPacker_2111_);
lean_dec_ref(v_preDefs_2109_);
v_a_2218_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2131_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2131_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2226_ = _args[0];
lean_object* v_perms_2227_ = _args[1];
lean_object* v_argsPacker_2228_ = _args[2];
lean_object* v___x_2229_ = _args[3];
lean_object* v_ref_2230_ = _args[4];
lean_object* v_kind_2231_ = _args[5];
lean_object* v_levelParams_2232_ = _args[6];
lean_object* v_modifiers_2233_ = _args[7];
lean_object* v_newFn_2234_ = _args[8];
lean_object* v_binders_2235_ = _args[9];
lean_object* v_numSectionVars_2236_ = _args[10];
lean_object* v_value_2237_ = _args[11];
lean_object* v_termination_2238_ = _args[12];
lean_object* v_fixedParamPerms_2239_ = _args[13];
lean_object* v_ys_2240_ = _args[14];
lean_object* v___y_2241_ = _args[15];
lean_object* v___y_2242_ = _args[16];
lean_object* v___y_2243_ = _args[17];
lean_object* v___y_2244_ = _args[18];
lean_object* v___y_2245_ = _args[19];
_start:
{
uint8_t v___x_2504__boxed_2246_; uint8_t v_kind_boxed_2247_; lean_object* v_res_2248_; 
v___x_2504__boxed_2246_ = lean_unbox(v___x_2229_);
v_kind_boxed_2247_ = lean_unbox(v_kind_2231_);
v_res_2248_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2226_, v_perms_2227_, v_argsPacker_2228_, v___x_2504__boxed_2246_, v_ref_2230_, v_kind_boxed_2247_, v_levelParams_2232_, v_modifiers_2233_, v_newFn_2234_, v_binders_2235_, v_numSectionVars_2236_, v_value_2237_, v_termination_2238_, v_fixedParamPerms_2239_, v_ys_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v_perms_2227_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2249_, lean_object* v_argsPacker_2250_, lean_object* v_preDefs_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_ref_2260_; uint8_t v_kind_2261_; lean_object* v_levelParams_2262_; lean_object* v_modifiers_2263_; lean_object* v_declName_2264_; lean_object* v_binders_2265_; lean_object* v_numSectionVars_2266_; lean_object* v_type_2267_; lean_object* v_value_2268_; lean_object* v_termination_2269_; lean_object* v_newFn_2270_; uint8_t v___x_2271_; 
v___x_2257_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = lean_array_get_borrowed(v___x_2257_, v_preDefs_2251_, v___x_2258_);
v_ref_2260_ = lean_ctor_get(v___x_2259_, 0);
v_kind_2261_ = lean_ctor_get_uint8(v___x_2259_, sizeof(void*)*9);
v_levelParams_2262_ = lean_ctor_get(v___x_2259_, 1);
v_modifiers_2263_ = lean_ctor_get(v___x_2259_, 2);
v_declName_2264_ = lean_ctor_get(v___x_2259_, 3);
v_binders_2265_ = lean_ctor_get(v___x_2259_, 4);
v_numSectionVars_2266_ = lean_ctor_get(v___x_2259_, 5);
v_type_2267_ = lean_ctor_get(v___x_2259_, 6);
v_value_2268_ = lean_ctor_get(v___x_2259_, 7);
v_termination_2269_ = lean_ctor_get(v___x_2259_, 8);
lean_inc_ref(v_fixedParamPerms_2249_);
v_newFn_2270_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2249_, v_argsPacker_2250_, v_preDefs_2251_);
v___x_2271_ = lean_name_eq(v_newFn_2270_, v_declName_2264_);
if (v___x_2271_ == 0)
{
lean_object* v_perms_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_inc_ref(v_termination_2269_);
lean_inc_ref(v_value_2268_);
lean_inc_ref(v_type_2267_);
lean_inc(v_numSectionVars_2266_);
lean_inc(v_binders_2265_);
lean_inc_ref(v_modifiers_2263_);
lean_inc(v_levelParams_2262_);
lean_inc(v_ref_2260_);
v_perms_2272_ = lean_ctor_get(v_fixedParamPerms_2249_, 1);
lean_inc_ref_n(v_perms_2272_, 2);
v___x_2273_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2274_ = lean_box(v___x_2271_);
v___x_2275_ = lean_box(v_kind_2261_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2276_, 0, v_preDefs_2251_);
lean_closure_set(v___f_2276_, 1, v_perms_2272_);
lean_closure_set(v___f_2276_, 2, v_argsPacker_2250_);
lean_closure_set(v___f_2276_, 3, v___x_2274_);
lean_closure_set(v___f_2276_, 4, v_ref_2260_);
lean_closure_set(v___f_2276_, 5, v___x_2275_);
lean_closure_set(v___f_2276_, 6, v_levelParams_2262_);
lean_closure_set(v___f_2276_, 7, v_modifiers_2263_);
lean_closure_set(v___f_2276_, 8, v_newFn_2270_);
lean_closure_set(v___f_2276_, 9, v_binders_2265_);
lean_closure_set(v___f_2276_, 10, v_numSectionVars_2266_);
lean_closure_set(v___f_2276_, 11, v_value_2268_);
lean_closure_set(v___f_2276_, 12, v_termination_2269_);
lean_closure_set(v___f_2276_, 13, v_fixedParamPerms_2249_);
v___x_2277_ = lean_array_get(v___x_2273_, v_perms_2272_, v___x_2258_);
lean_dec_ref(v_perms_2272_);
v___x_2278_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2277_, v_type_2267_, v___f_2276_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
lean_inc(v___x_2259_);
lean_dec(v_newFn_2270_);
lean_dec_ref(v_preDefs_2251_);
lean_dec_ref(v_argsPacker_2250_);
lean_dec_ref(v_fixedParamPerms_2249_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2259_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2280_, lean_object* v_argsPacker_2281_, lean_object* v_preDefs_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2280_, v_argsPacker_2281_, v_preDefs_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2289_, lean_object* v_ys_2290_, lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_bs_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2289_, v_ys_2290_, v_sz_2292_, v_i_2293_, v_bs_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2301_, lean_object* v_ys_2302_, lean_object* v_as_2303_, lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_bs_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
size_t v_sz_boxed_2312_; size_t v_i_boxed_2313_; lean_object* v_res_2314_; 
v_sz_boxed_2312_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2313_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2314_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2301_, v_ys_2302_, v_as_2303_, v_sz_boxed_2312_, v_i_boxed_2313_, v_bs_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_as_2303_);
lean_dec_ref(v___x_2301_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2315_, lean_object* v_ys_2316_, lean_object* v_as_2317_, size_t v_sz_2318_, size_t v_i_2319_, lean_object* v_bs_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2315_, v_ys_2316_, v_sz_2318_, v_i_2319_, v_bs_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2327_, lean_object* v_ys_2328_, lean_object* v_as_2329_, lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_bs_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2327_, v_ys_2328_, v_as_2329_, v_sz_boxed_2338_, v_i_boxed_2339_, v_bs_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec_ref(v_as_2329_);
lean_dec_ref(v___x_2327_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2341_, lean_object* v_k_2342_, uint8_t v_cleanupAnnotations_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___f_2349_; uint8_t v___x_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2349_, 0, v_k_2342_);
v___x_2350_ = 1;
v___x_2351_ = 0;
v___x_2352_ = lean_box(0);
v___x_2353_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2341_, v___x_2350_, v___x_2351_, v___x_2350_, v___x_2351_, v___x_2352_, v___f_2349_, v_cleanupAnnotations_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2353_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2353_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2370_, lean_object* v_k_2371_, lean_object* v_cleanupAnnotations_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2378_; lean_object* v_res_2379_; 
v_cleanupAnnotations_boxed_2378_ = lean_unbox(v_cleanupAnnotations_2372_);
v_res_2379_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2370_, v_k_2371_, v_cleanupAnnotations_boxed_2378_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2380_, lean_object* v_e_2381_, lean_object* v_k_2382_, uint8_t v_cleanupAnnotations_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2381_, v_k_2382_, v_cleanupAnnotations_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2390_, lean_object* v_e_2391_, lean_object* v_k_2392_, lean_object* v_cleanupAnnotations_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2399_; lean_object* v_res_2400_; 
v_cleanupAnnotations_boxed_2399_ = lean_unbox(v_cleanupAnnotations_2393_);
v_res_2400_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2390_, v_e_2391_, v_k_2392_, v_cleanupAnnotations_boxed_2399_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___f_2407_; lean_object* v___x_1649__overap_2408_; lean_object* v___x_2409_; 
v___f_2407_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2408_ = lean_panic_fn_borrowed(v___f_2407_, v_msg_2401_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
v___x_2409_ = lean_apply_5(v___x_1649__overap_2408_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, lean_box(0));
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2417_, lean_object* v_x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_array_get_size(v_xs_2417_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2426_, lean_object* v_x_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2426_, v_x_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_x_2427_);
lean_dec_ref(v_xs_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_a_2443_; uint8_t v___x_2447_; 
v___x_2447_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v_b_2437_);
return v___x_2448_;
}
else
{
lean_object* v_snd_2449_; lean_object* v_fst_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2494_; 
v_snd_2449_ = lean_ctor_get(v_b_2437_, 1);
v_fst_2450_ = lean_ctor_get(v_b_2437_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_b_2437_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2452_ = v_b_2437_;
v_isShared_2453_ = v_isSharedCheck_2494_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snd_2449_);
lean_inc(v_fst_2450_);
lean_dec(v_b_2437_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2494_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_array_2454_; lean_object* v_start_2455_; lean_object* v_stop_2456_; uint8_t v___x_2457_; 
v_array_2454_ = lean_ctor_get(v_snd_2449_, 0);
v_start_2455_ = lean_ctor_get(v_snd_2449_, 1);
v_stop_2456_ = lean_ctor_get(v_snd_2449_, 2);
v___x_2457_ = lean_nat_dec_lt(v_start_2455_, v_stop_2456_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2459_; 
if (v_isShared_2453_ == 0)
{
v___x_2459_ = v___x_2452_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_fst_2450_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_snd_2449_);
v___x_2459_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
else
{
lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2490_; 
lean_inc(v_stop_2456_);
lean_inc(v_start_2455_);
lean_inc_ref(v_array_2454_);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_snd_2449_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; 
v_unused_2491_ = lean_ctor_get(v_snd_2449_, 2);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_snd_2449_, 1);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_snd_2449_, 0);
lean_dec(v_unused_2493_);
v___x_2463_ = v_snd_2449_;
v_isShared_2464_ = v_isSharedCheck_2490_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v_snd_2449_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2490_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2465_ = lean_array_fget(v_array_2454_, v_start_2455_);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_nat_add(v_start_2455_, v___x_2466_);
lean_dec(v_start_2455_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v___x_2467_);
v___x_2469_ = v___x_2463_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_array_2454_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_stop_2456_);
v___x_2469_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_a_2470_ = lean_array_uget_borrowed(v_as_2434_, v_i_2436_);
v___x_2471_ = l_Lean_Expr_fvarId_x21(v_a_2470_);
v___x_2472_ = l_Lean_FVarId_getUserName___redArg(v___x_2471_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = lean_array_push(v_fst_2450_, v_a_2473_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2469_);
lean_ctor_set(v___x_2452_, 0, v___x_2474_);
v___x_2476_ = v___x_2452_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2469_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
v_a_2443_ = v___x_2476_;
goto v___jp_2442_;
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___x_2469_);
lean_del_object(v___x_2452_);
lean_dec(v_fst_2450_);
v_a_2478_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2472_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2472_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v___x_2487_; 
lean_dec_ref_known(v___x_2465_, 1);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2469_);
v___x_2487_ = v___x_2452_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_fst_2450_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2469_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
v_a_2443_ = v___x_2487_;
goto v___jp_2442_;
}
}
}
}
}
}
}
v___jp_2442_:
{
size_t v___x_2444_; size_t v___x_2445_; 
v___x_2444_ = ((size_t)1ULL);
v___x_2445_ = lean_usize_add(v_i_2436_, v___x_2444_);
v_i_2436_ = v___x_2445_;
v_b_2437_ = v_a_2443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2495_, lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_b_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2495_, v_sz_boxed_2503_, v_i_boxed_2504_, v_b_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_as_2495_);
return v_res_2505_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2508_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2509_ = lean_unsigned_to_nat(4u);
v___x_2510_ = lean_unsigned_to_nat(119u);
v___x_2511_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2512_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2513_ = l_mkPanicMessageWithDecl(v___x_2512_, v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2515_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2516_ = lean_unsigned_to_nat(4u);
v___x_2517_ = lean_unsigned_to_nat(120u);
v___x_2518_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2519_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2520_ = l_mkPanicMessageWithDecl(v___x_2519_, v___x_2518_, v___x_2517_, v___x_2516_, v___x_2515_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2523_, lean_object* v_fixedParamPerms_2524_, lean_object* v___x_2525_, lean_object* v_preDefIdx_2526_, lean_object* v_xs_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = lean_array_get_size(v_xs_2527_);
v___x_2535_ = lean_nat_dec_eq(v___x_2534_, v_a_2523_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2537_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2536_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2537_;
}
else
{
lean_object* v_perms_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v_perms_2538_ = lean_ctor_get(v_fixedParamPerms_2524_, 1);
v___x_2539_ = lean_array_get_borrowed(v___x_2525_, v_perms_2538_, v_preDefIdx_2526_);
v___x_2540_ = lean_array_get_size(v___x_2539_);
v___x_2541_ = lean_nat_dec_eq(v___x_2540_, v_a_2523_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2543_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2542_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2539_);
v___x_2546_ = l_Array_toSubarray___redArg(v___x_2539_, v___x_2544_, v___x_2540_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v_sz_2548_ = lean_array_size(v_xs_2527_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2527_, v_sz_2548_, v___x_2549_, v___x_2547_, v___y_2529_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2559_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2559_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2559_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v_fst_2555_; lean_object* v___x_2557_; 
v_fst_2555_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_fst_2555_);
lean_dec(v_a_2551_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v_fst_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_fst_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2550_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2550_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2568_, lean_object* v_fixedParamPerms_2569_, lean_object* v___x_2570_, lean_object* v_preDefIdx_2571_, lean_object* v_xs_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2568_, v_fixedParamPerms_2569_, v___x_2570_, v_preDefIdx_2571_, v_xs_2572_, v_x_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v_x_2573_);
lean_dec_ref(v_xs_2572_);
lean_dec(v_preDefIdx_2571_);
lean_dec_ref(v___x_2570_);
lean_dec_ref(v_fixedParamPerms_2569_);
lean_dec(v_a_2568_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2581_, lean_object* v_preDefIdx_2582_, lean_object* v_preDef_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_type_2589_; lean_object* v_value_2590_; lean_object* v___f_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; 
v_type_2589_ = lean_ctor_get(v_preDef_2583_, 6);
lean_inc_ref(v_type_2589_);
v_value_2590_ = lean_ctor_get(v_preDef_2583_, 7);
lean_inc_ref(v_value_2590_);
lean_dec_ref(v_preDef_2583_);
v___f_2591_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2592_ = 0;
v___x_2593_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2590_, v___f_2591_, v___x_2592_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_n(v_a_2594_, 2);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___f_2596_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2596_, 0, v_a_2594_);
lean_closure_set(v___f_2596_, 1, v_fixedParamPerms_2581_);
lean_closure_set(v___f_2596_, 2, v___x_2595_);
lean_closure_set(v___f_2596_, 3, v_preDefIdx_2582_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_a_2594_);
v___x_2598_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2589_, v___x_2597_, v___f_2596_, v___x_2592_, v___x_2592_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_type_2589_);
lean_dec(v_preDefIdx_2582_);
lean_dec_ref(v_fixedParamPerms_2581_);
v_a_2599_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2593_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2593_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2607_, lean_object* v_preDefIdx_2608_, lean_object* v_preDef_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2607_, v_preDefIdx_2608_, v_preDef_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2616_, size_t v_sz_2617_, size_t v_i_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2616_, v_sz_2617_, v_i_2618_, v_b_2619_, v___y_2620_, v___y_2622_, v___y_2623_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2626_, lean_object* v_sz_2627_, lean_object* v_i_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
size_t v_sz_boxed_2635_; size_t v_i_boxed_2636_; lean_object* v_res_2637_; 
v_sz_boxed_2635_ = lean_unbox_usize(v_sz_2627_);
lean_dec(v_sz_2627_);
v_i_boxed_2636_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_res_2637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2626_, v_sz_boxed_2635_, v_i_boxed_2636_, v_b_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v_as_2626_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___f_2644_; lean_object* v___x_1578__overap_2645_; lean_object* v___x_2646_; 
v___f_2644_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1578__overap_2645_ = lean_panic_fn_borrowed(v___f_2644_, v_msg_2638_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2639_);
v___x_2646_ = lean_apply_5(v___x_1578__overap_2645_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, lean_box(0));
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2653_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2654_; double v___x_2655_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_float_of_nat(v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2659_, lean_object* v_msg_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_ref_2666_; lean_object* v___x_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2712_; 
v_ref_2666_ = lean_ctor_get(v___y_2663_, 2);
v___x_2667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2712_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2712_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v_traceState_2673_; lean_object* v_env_2674_; lean_object* v_nextMacroScope_2675_; lean_object* v_ngen_2676_; lean_object* v_auxDeclNGen_2677_; lean_object* v_cache_2678_; lean_object* v_messages_2679_; lean_object* v_infoState_2680_; lean_object* v_snapshotTasks_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2711_; 
v___x_2672_ = lean_st_ref_take(v___y_2664_);
v_traceState_2673_ = lean_ctor_get(v___x_2672_, 4);
v_env_2674_ = lean_ctor_get(v___x_2672_, 0);
v_nextMacroScope_2675_ = lean_ctor_get(v___x_2672_, 1);
v_ngen_2676_ = lean_ctor_get(v___x_2672_, 2);
v_auxDeclNGen_2677_ = lean_ctor_get(v___x_2672_, 3);
v_cache_2678_ = lean_ctor_get(v___x_2672_, 5);
v_messages_2679_ = lean_ctor_get(v___x_2672_, 6);
v_infoState_2680_ = lean_ctor_get(v___x_2672_, 7);
v_snapshotTasks_2681_ = lean_ctor_get(v___x_2672_, 8);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2683_ = v___x_2672_;
v_isShared_2684_ = v_isSharedCheck_2711_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snapshotTasks_2681_);
lean_inc(v_infoState_2680_);
lean_inc(v_messages_2679_);
lean_inc(v_cache_2678_);
lean_inc(v_traceState_2673_);
lean_inc(v_auxDeclNGen_2677_);
lean_inc(v_ngen_2676_);
lean_inc(v_nextMacroScope_2675_);
lean_inc(v_env_2674_);
lean_dec(v___x_2672_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2711_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
uint64_t v_tid_2685_; lean_object* v_traces_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2710_; 
v_tid_2685_ = lean_ctor_get_uint64(v_traceState_2673_, sizeof(void*)*1);
v_traces_2686_ = lean_ctor_get(v_traceState_2673_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_traceState_2673_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2688_ = v_traceState_2673_;
v_isShared_2689_ = v_isSharedCheck_2710_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_traces_2686_);
lean_dec(v_traceState_2673_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2710_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; double v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2692_ = 0;
v___x_2693_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2694_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2694_, 0, v_cls_2659_);
lean_ctor_set(v___x_2694_, 1, v___x_2690_);
lean_ctor_set(v___x_2694_, 2, v___x_2693_);
lean_ctor_set_float(v___x_2694_, sizeof(void*)*3, v___x_2691_);
lean_ctor_set_float(v___x_2694_, sizeof(void*)*3 + 8, v___x_2691_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*3 + 16, v___x_2692_);
v___x_2695_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2696_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v_a_2668_);
lean_ctor_set(v___x_2696_, 2, v___x_2695_);
lean_inc(v_ref_2666_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_ref_2666_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_PersistentArray_push___redArg(v_traces_2686_, v___x_2697_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2698_);
v___x_2700_ = v___x_2688_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2698_);
lean_ctor_set_uint64(v_reuseFailAlloc_2709_, sizeof(void*)*1, v_tid_2685_);
v___x_2700_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 4, v___x_2700_);
v___x_2702_ = v___x_2683_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_env_2674_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_nextMacroScope_2675_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_ngen_2676_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_auxDeclNGen_2677_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2708_, 5, v_cache_2678_);
lean_ctor_set(v_reuseFailAlloc_2708_, 6, v_messages_2679_);
lean_ctor_set(v_reuseFailAlloc_2708_, 7, v_infoState_2680_);
lean_ctor_set(v_reuseFailAlloc_2708_, 8, v_snapshotTasks_2681_);
v___x_2702_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2703_ = lean_st_ref_put(v___y_2664_, v___x_2702_);
v___x_2704_ = lean_box(0);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2704_);
v___x_2706_ = v___x_2670_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2713_, lean_object* v_msg_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2713_, v_msg_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2724_ = lean_unsigned_to_nat(8u);
v___x_2725_ = lean_unsigned_to_nat(135u);
v___x_2726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2727_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2728_ = l_mkPanicMessageWithDecl(v___x_2727_, v___x_2726_, v___x_2725_, v___x_2724_, v___x_2723_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2729_, lean_object* v_unaryPreDefNonRec_2730_, lean_object* v___x_2731_, lean_object* v_us_2732_, lean_object* v_argsPacker_2733_, lean_object* v___x_2734_, lean_object* v_params_2735_, lean_object* v_x_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_array_get_size(v_params_2735_);
v___x_2743_ = lean_nat_dec_eq(v___x_2729_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec(v___x_2734_);
lean_dec(v_us_2732_);
lean_dec_ref(v_unaryPreDefNonRec_2730_);
v___x_2744_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2745_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2744_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2745_;
}
else
{
lean_object* v_declName_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_declName_2746_ = lean_ctor_get(v_unaryPreDefNonRec_2730_, 3);
lean_inc(v_declName_2746_);
lean_dec_ref(v_unaryPreDefNonRec_2730_);
v___x_2747_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2731_, v_params_2735_);
v___x_2748_ = l_Lean_mkConst(v_declName_2746_, v_us_2732_);
v___x_2749_ = l_Lean_mkAppN(v___x_2748_, v___x_2747_);
lean_dec_ref(v___x_2747_);
v___x_2750_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2733_, v___x_2749_, v___x_2734_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2731_, v_params_2735_);
v___x_2753_ = l_Lean_Expr_beta(v_a_2751_, v___x_2752_);
v___x_2754_ = 0;
v___x_2755_ = 1;
v___x_2756_ = l_Lean_Meta_mkLambdaFVars(v_params_2735_, v___x_2753_, v___x_2754_, v___x_2743_, v___x_2754_, v___x_2743_, v___x_2755_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2756_;
}
else
{
return v___x_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2757_, lean_object* v_unaryPreDefNonRec_2758_, lean_object* v___x_2759_, lean_object* v_us_2760_, lean_object* v_argsPacker_2761_, lean_object* v___x_2762_, lean_object* v_params_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2757_, v_unaryPreDefNonRec_2758_, v___x_2759_, v_us_2760_, v_argsPacker_2761_, v___x_2762_, v_params_2763_, v_x_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v_x_2764_);
lean_dec_ref(v_params_2763_);
lean_dec_ref(v_argsPacker_2761_);
lean_dec_ref(v___x_2759_);
lean_dec(v___x_2757_);
return v_res_2770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2783_ = l_Lean_Name_append(v___x_2782_, v___x_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2787_, lean_object* v_unaryPreDefNonRec_2788_, lean_object* v_us_2789_, lean_object* v_argsPacker_2790_, size_t v_sz_2791_, size_t v_i_2792_, lean_object* v_bs_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_usize_dec_lt(v_i_2792_, v_sz_2791_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v_argsPacker_2790_);
lean_dec(v_us_2789_);
lean_dec_ref(v_unaryPreDefNonRec_2788_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_bs_2793_);
return v___x_2800_;
}
else
{
lean_object* v_v_2801_; lean_object* v_perms_2802_; lean_object* v_ref_2803_; uint8_t v_kind_2804_; lean_object* v_levelParams_2805_; lean_object* v_modifiers_2806_; lean_object* v_declName_2807_; lean_object* v_binders_2808_; lean_object* v_numSectionVars_2809_; lean_object* v_type_2810_; lean_object* v_termination_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2863_; 
v_v_2801_ = lean_array_uget(v_bs_2793_, v_i_2792_);
v_perms_2802_ = lean_ctor_get(v_fixedParamPerms_2787_, 1);
v_ref_2803_ = lean_ctor_get(v_v_2801_, 0);
v_kind_2804_ = lean_ctor_get_uint8(v_v_2801_, sizeof(void*)*9);
v_levelParams_2805_ = lean_ctor_get(v_v_2801_, 1);
v_modifiers_2806_ = lean_ctor_get(v_v_2801_, 2);
v_declName_2807_ = lean_ctor_get(v_v_2801_, 3);
v_binders_2808_ = lean_ctor_get(v_v_2801_, 4);
v_numSectionVars_2809_ = lean_ctor_get(v_v_2801_, 5);
v_type_2810_ = lean_ctor_get(v_v_2801_, 6);
v_termination_2811_ = lean_ctor_get(v_v_2801_, 8);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_v_2801_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v_v_2801_, 7);
lean_dec(v_unused_2864_);
v___x_2813_ = v_v_2801_;
v_isShared_2814_ = v_isSharedCheck_2863_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_termination_2811_);
lean_inc(v_type_2810_);
lean_inc(v_numSectionVars_2809_);
lean_inc(v_binders_2808_);
lean_inc(v_declName_2807_);
lean_inc(v_modifiers_2806_);
lean_inc(v_levelParams_2805_);
lean_inc(v_ref_2803_);
lean_dec(v_v_2801_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2863_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v_bs_x27_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; 
v___x_2815_ = lean_unsigned_to_nat(0u);
v_bs_x27_2816_ = lean_array_uset(v_bs_2793_, v_i_2792_, v___x_2815_);
v___x_2817_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2818_ = lean_usize_to_nat(v_i_2792_);
v___x_2819_ = lean_array_get_borrowed(v___x_2817_, v_perms_2802_, v___x_2818_);
v___x_2820_ = lean_array_get_size(v___x_2819_);
lean_inc_ref(v_argsPacker_2790_);
lean_inc(v_us_2789_);
lean_inc(v___x_2819_);
lean_inc_ref(v_unaryPreDefNonRec_2788_);
v___f_2821_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2821_, 0, v___x_2820_);
lean_closure_set(v___f_2821_, 1, v_unaryPreDefNonRec_2788_);
lean_closure_set(v___f_2821_, 2, v___x_2819_);
lean_closure_set(v___f_2821_, 3, v_us_2789_);
lean_closure_set(v___f_2821_, 4, v_argsPacker_2790_);
lean_closure_set(v___f_2821_, 5, v___x_2818_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
v___x_2823_ = 0;
lean_inc_ref(v_type_2810_);
v___x_2824_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2810_, v___x_2822_, v___f_2821_, v___x_2823_, v___x_2823_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v_toCold_2834_; lean_object* v_options_2835_; uint8_t v_hasTrace_2836_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v_toCold_2834_ = lean_ctor_get(v___y_2796_, 0);
v_options_2835_ = lean_ctor_get(v_toCold_2834_, 2);
v_hasTrace_2836_ = lean_ctor_get_uint8(v_options_2835_, sizeof(void*)*1);
if (v_hasTrace_2836_ == 0)
{
goto v___jp_2826_;
}
else
{
lean_object* v_inheritedTraceOptions_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v_inheritedTraceOptions_2837_ = lean_ctor_get(v_toCold_2834_, 11);
v___x_2838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2837_, v_options_2835_, v___x_2839_);
if (v___x_2840_ == 0)
{
goto v___jp_2826_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_inc(v_declName_2807_);
v___x_2841_ = l_Lean_MessageData_ofName(v_declName_2807_);
v___x_2842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
lean_inc(v_a_2825_);
v___x_2844_ = l_Lean_MessageData_ofExpr(v_a_2825_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2838_, v___x_2845_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec_ref_known(v___x_2846_, 1);
goto v___jp_2826_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2825_);
lean_dec_ref(v_bs_x27_2816_);
lean_del_object(v___x_2813_);
lean_dec_ref(v_termination_2811_);
lean_dec_ref(v_type_2810_);
lean_dec(v_numSectionVars_2809_);
lean_dec(v_binders_2808_);
lean_dec(v_declName_2807_);
lean_dec_ref(v_modifiers_2806_);
lean_dec(v_levelParams_2805_);
lean_dec(v_ref_2803_);
lean_dec_ref(v_argsPacker_2790_);
lean_dec(v_us_2789_);
lean_dec_ref(v_unaryPreDefNonRec_2788_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
v___jp_2826_:
{
lean_object* v___x_2828_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 7, v_a_2825_);
v___x_2828_ = v___x_2813_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_ref_2803_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_levelParams_2805_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_modifiers_2806_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_declName_2807_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_binders_2808_);
lean_ctor_set(v_reuseFailAlloc_2833_, 5, v_numSectionVars_2809_);
lean_ctor_set(v_reuseFailAlloc_2833_, 6, v_type_2810_);
lean_ctor_set(v_reuseFailAlloc_2833_, 7, v_a_2825_);
lean_ctor_set(v_reuseFailAlloc_2833_, 8, v_termination_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*9, v_kind_2804_);
v___x_2828_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_add(v_i_2792_, v___x_2829_);
v___x_2831_ = lean_array_uset(v_bs_x27_2816_, v_i_2792_, v___x_2828_);
v_i_2792_ = v___x_2830_;
v_bs_2793_ = v___x_2831_;
goto _start;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref(v_bs_x27_2816_);
lean_del_object(v___x_2813_);
lean_dec_ref(v_termination_2811_);
lean_dec_ref(v_type_2810_);
lean_dec(v_numSectionVars_2809_);
lean_dec(v_binders_2808_);
lean_dec(v_declName_2807_);
lean_dec_ref(v_modifiers_2806_);
lean_dec(v_levelParams_2805_);
lean_dec(v_ref_2803_);
lean_dec_ref(v_argsPacker_2790_);
lean_dec(v_us_2789_);
lean_dec_ref(v_unaryPreDefNonRec_2788_);
v_a_2855_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2824_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2824_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2865_, lean_object* v_unaryPreDefNonRec_2866_, lean_object* v_us_2867_, lean_object* v_argsPacker_2868_, lean_object* v_sz_2869_, lean_object* v_i_2870_, lean_object* v_bs_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2869_);
lean_dec(v_sz_2869_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2870_);
lean_dec(v_i_2870_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2865_, v_unaryPreDefNonRec_2866_, v_us_2867_, v_argsPacker_2868_, v_sz_boxed_2877_, v_i_boxed_2878_, v_bs_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v_fixedParamPerms_2865_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2880_, lean_object* v_preDefs_2881_, lean_object* v_fixedParamPerms_2882_, lean_object* v_us_2883_, lean_object* v_argsPacker_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2880_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2890_) == 0)
{
size_t v_sz_2891_; size_t v___x_2892_; lean_object* v___x_2893_; 
lean_dec_ref_known(v___x_2890_, 1);
v_sz_2891_ = lean_array_size(v_preDefs_2881_);
v___x_2892_ = ((size_t)0ULL);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2882_, v_unaryPreDefNonRec_2880_, v_us_2883_, v_argsPacker_2884_, v_sz_2891_, v___x_2892_, v_preDefs_2881_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2893_;
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v_argsPacker_2884_);
lean_dec(v_us_2883_);
lean_dec_ref(v_preDefs_2881_);
lean_dec_ref(v_unaryPreDefNonRec_2880_);
v_a_2894_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2890_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2890_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2902_, lean_object* v_preDefs_2903_, lean_object* v_fixedParamPerms_2904_, lean_object* v_us_2905_, lean_object* v_argsPacker_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2902_, v_preDefs_2903_, v_fixedParamPerms_2904_, v_us_2905_, v_argsPacker_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v_fixedParamPerms_2904_);
return v_res_2912_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2913_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2919_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
lean_ctor_set(v___x_2919_, 2, v___x_2918_);
lean_ctor_set(v___x_2919_, 3, v___x_2918_);
lean_ctor_set(v___x_2919_, 4, v___x_2918_);
lean_ctor_set(v___x_2919_, 5, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; lean_object* v_nextMacroScope_2925_; lean_object* v_ngen_2926_; lean_object* v_auxDeclNGen_2927_; lean_object* v_traceState_2928_; lean_object* v_messages_2929_; lean_object* v_infoState_2930_; lean_object* v_snapshotTasks_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2957_; 
v___x_2924_ = lean_st_ref_take(v___y_2922_);
v_nextMacroScope_2925_ = lean_ctor_get(v___x_2924_, 1);
v_ngen_2926_ = lean_ctor_get(v___x_2924_, 2);
v_auxDeclNGen_2927_ = lean_ctor_get(v___x_2924_, 3);
v_traceState_2928_ = lean_ctor_get(v___x_2924_, 4);
v_messages_2929_ = lean_ctor_get(v___x_2924_, 6);
v_infoState_2930_ = lean_ctor_get(v___x_2924_, 7);
v_snapshotTasks_2931_ = lean_ctor_get(v___x_2924_, 8);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; lean_object* v_unused_2959_; 
v_unused_2958_ = lean_ctor_get(v___x_2924_, 5);
lean_dec(v_unused_2958_);
v_unused_2959_ = lean_ctor_get(v___x_2924_, 0);
lean_dec(v_unused_2959_);
v___x_2933_ = v___x_2924_;
v_isShared_2934_ = v_isSharedCheck_2957_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snapshotTasks_2931_);
lean_inc(v_infoState_2930_);
lean_inc(v_messages_2929_);
lean_inc(v_traceState_2928_);
lean_inc(v_auxDeclNGen_2927_);
lean_inc(v_ngen_2926_);
lean_inc(v_nextMacroScope_2925_);
lean_dec(v___x_2924_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2957_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 5, v___x_2935_);
lean_ctor_set(v___x_2933_, 0, v_env_2920_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_env_2920_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_nextMacroScope_2925_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_ngen_2926_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_auxDeclNGen_2927_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v_traceState_2928_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_messages_2929_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_infoState_2930_);
lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_snapshotTasks_2931_);
v___x_2937_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_mctx_2940_; lean_object* v_zetaDeltaFVarIds_2941_; lean_object* v_postponed_2942_; lean_object* v_diag_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2954_; 
v___x_2938_ = lean_st_ref_put(v___y_2922_, v___x_2937_);
v___x_2939_ = lean_st_ref_take(v___y_2921_);
v_mctx_2940_ = lean_ctor_get(v___x_2939_, 0);
v_zetaDeltaFVarIds_2941_ = lean_ctor_get(v___x_2939_, 2);
v_postponed_2942_ = lean_ctor_get(v___x_2939_, 3);
v_diag_2943_ = lean_ctor_get(v___x_2939_, 4);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v___x_2939_, 1);
lean_dec(v_unused_2955_);
v___x_2945_ = v___x_2939_;
v_isShared_2946_ = v_isSharedCheck_2954_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_diag_2943_);
lean_inc(v_postponed_2942_);
lean_inc(v_zetaDeltaFVarIds_2941_);
lean_inc(v_mctx_2940_);
lean_dec(v___x_2939_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2954_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_mctx_2940_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_zetaDeltaFVarIds_2941_);
lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_postponed_2942_);
lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_diag_2943_);
v___x_2949_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_st_ref_put(v___y_2921_, v___x_2949_);
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v_env_2973_; lean_object* v_a_2975_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2972_ = lean_st_ref_get(v___y_2970_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc_ref(v_env_2973_);
lean_dec(v___x_2972_);
v___x_2985_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2965_, v___y_2968_, v___y_2970_);
lean_dec_ref(v___x_2985_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v___x_2986_ = lean_apply_5(v_x_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, lean_box(0));
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2973_, v___y_2968_, v___y_2970_);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v___x_2988_, 0);
lean_dec(v_unused_2996_);
v___x_2990_ = v___x_2988_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v___x_2988_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v_a_2987_);
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2987_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2986_, 1);
v_a_2975_ = v_a_2997_;
goto v___jp_2974_;
}
v___jp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
v___x_2976_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2973_, v___y_2968_, v___y_2970_);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v___x_2976_, 0);
lean_dec(v_unused_2984_);
v___x_2978_ = v___x_2976_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v___x_2976_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 1);
lean_ctor_set(v___x_2978_, 0, v_a_2975_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2975_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_2998_, lean_object* v_x_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_2998_, v_x_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3006_, lean_object* v_argsPacker_3007_, lean_object* v_preDefs_3008_, lean_object* v_unaryPreDefNonRec_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3015_; lean_object* v_levelParams_3016_; lean_object* v_env_3017_; lean_object* v___x_3018_; lean_object* v_us_3019_; lean_object* v___f_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3015_ = lean_st_ref_get(v_a_3013_);
v_levelParams_3016_ = lean_ctor_get(v_unaryPreDefNonRec_3009_, 1);
v_env_3017_ = lean_ctor_get(v___x_3015_, 0);
lean_inc_ref(v_env_3017_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
lean_inc(v_levelParams_3016_);
v_us_3019_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3016_, v___x_3018_);
v___f_3020_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3020_, 0, v_unaryPreDefNonRec_3009_);
lean_closure_set(v___f_3020_, 1, v_preDefs_3008_);
lean_closure_set(v___f_3020_, 2, v_fixedParamPerms_3006_);
lean_closure_set(v___f_3020_, 3, v_us_3019_);
lean_closure_set(v___f_3020_, 4, v_argsPacker_3007_);
v___x_3021_ = l_Lean_Environment_unlockAsync(v_env_3017_);
v___x_3022_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3021_, v___f_3020_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3023_, lean_object* v_argsPacker_3024_, lean_object* v_preDefs_3025_, lean_object* v_unaryPreDefNonRec_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3023_, v_argsPacker_3024_, v_preDefs_3025_, v_unaryPreDefNonRec_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3033_, lean_object* v_unaryPreDefNonRec_3034_, lean_object* v_us_3035_, lean_object* v_argsPacker_3036_, lean_object* v_as_3037_, size_t v_sz_3038_, size_t v_i_3039_, lean_object* v_bs_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3033_, v_unaryPreDefNonRec_3034_, v_us_3035_, v_argsPacker_3036_, v_sz_3038_, v_i_3039_, v_bs_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3047_, lean_object* v_unaryPreDefNonRec_3048_, lean_object* v_us_3049_, lean_object* v_argsPacker_3050_, lean_object* v_as_3051_, lean_object* v_sz_3052_, lean_object* v_i_3053_, lean_object* v_bs_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
size_t v_sz_boxed_3060_; size_t v_i_boxed_3061_; lean_object* v_res_3062_; 
v_sz_boxed_3060_ = lean_unbox_usize(v_sz_3052_);
lean_dec(v_sz_3052_);
v_i_boxed_3061_ = lean_unbox_usize(v_i_3053_);
lean_dec(v_i_3053_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3047_, v_unaryPreDefNonRec_3048_, v_us_3049_, v_argsPacker_3050_, v_as_3051_, v_sz_boxed_3060_, v_i_boxed_3061_, v_bs_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v_as_3051_);
lean_dec_ref(v_fixedParamPerms_3047_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3063_, v___y_3065_, v___y_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3077_, lean_object* v_env_3078_, lean_object* v_x_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3078_, v_x_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3086_, lean_object* v_env_3087_, lean_object* v_x_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3086_, v_env_3087_, v_x_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
return v_res_3094_;
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
