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
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_nbuckets_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_747_ = lean_array_get_size(v_data_746_);
v___x_748_ = lean_unsigned_to_nat(2u);
v_nbuckets_749_ = lean_nat_mul(v___x_747_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_box(0);
v___x_752_ = lean_mk_array(v_nbuckets_749_, v___x_751_);
v___x_753_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_750_, v_data_746_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_754_, lean_object* v_b_755_, lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_dec(v_b_755_);
lean_dec_ref(v_a_754_);
return v_x_756_;
}
else
{
lean_object* v_key_757_; lean_object* v_value_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_771_; 
v_key_757_ = lean_ctor_get(v_x_756_, 0);
v_value_758_ = lean_ctor_get(v_x_756_, 1);
v_tail_759_ = lean_ctor_get(v_x_756_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_771_ == 0)
{
v___x_761_ = v_x_756_;
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_inc(v_value_758_);
lean_inc(v_key_757_);
lean_dec(v_x_756_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = l_Lean_ExprStructEq_beq(v_key_757_, v_a_754_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_754_, v_b_755_, v_tail_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_764_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_key_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_value_758_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_769_; 
lean_dec(v_value_758_);
lean_dec(v_key_757_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_b_755_);
lean_ctor_set(v___x_761_, 0, v_a_754_);
v___x_769_ = v___x_761_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_754_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_b_755_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_tail_759_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_772_, lean_object* v_a_773_, lean_object* v_b_774_){
_start:
{
lean_object* v_size_775_; lean_object* v_buckets_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_819_; 
v_size_775_ = lean_ctor_get(v_m_772_, 0);
v_buckets_776_ = lean_ctor_get(v_m_772_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_m_772_);
if (v_isSharedCheck_819_ == 0)
{
v___x_778_ = v_m_772_;
v_isShared_779_ = v_isSharedCheck_819_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_buckets_776_);
lean_inc(v_size_775_);
lean_dec(v_m_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_819_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v_fold_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v_bkt_793_; uint8_t v___x_794_; 
v___x_780_ = lean_array_get_size(v_buckets_776_);
v___x_781_ = l_Lean_ExprStructEq_hash(v_a_773_);
v___x_782_ = 32ULL;
v___x_783_ = lean_uint64_shift_right(v___x_781_, v___x_782_);
v_fold_784_ = lean_uint64_xor(v___x_781_, v___x_783_);
v___x_785_ = 16ULL;
v___x_786_ = lean_uint64_shift_right(v_fold_784_, v___x_785_);
v___x_787_ = lean_uint64_xor(v_fold_784_, v___x_786_);
v___x_788_ = lean_uint64_to_usize(v___x_787_);
v___x_789_ = lean_usize_of_nat(v___x_780_);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_sub(v___x_789_, v___x_790_);
v___x_792_ = lean_usize_land(v___x_788_, v___x_791_);
v_bkt_793_ = lean_array_uget_borrowed(v_buckets_776_, v___x_792_);
v___x_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_773_, v_bkt_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v_size_x27_796_; lean_object* v___x_797_; lean_object* v_buckets_x27_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v_size_x27_796_ = lean_nat_add(v_size_775_, v___x_795_);
lean_dec(v_size_775_);
lean_inc(v_bkt_793_);
v___x_797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_797_, 0, v_a_773_);
lean_ctor_set(v___x_797_, 1, v_b_774_);
lean_ctor_set(v___x_797_, 2, v_bkt_793_);
v_buckets_x27_798_ = lean_array_uset(v_buckets_776_, v___x_792_, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(4u);
v___x_800_ = lean_nat_mul(v_size_x27_796_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(3u);
v___x_802_ = lean_nat_div(v___x_800_, v___x_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_array_get_size(v_buckets_x27_798_);
v___x_804_ = lean_nat_dec_le(v___x_802_, v___x_803_);
lean_dec(v___x_802_);
if (v___x_804_ == 0)
{
lean_object* v_val_805_; lean_object* v___x_807_; 
v_val_805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_798_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_val_805_);
lean_ctor_set(v___x_778_, 0, v_size_x27_796_);
v___x_807_ = v___x_778_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_size_x27_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_val_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_object* v___x_810_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_buckets_x27_798_);
lean_ctor_set(v___x_778_, 0, v_size_x27_796_);
v___x_810_ = v___x_778_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_size_x27_796_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_buckets_x27_798_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v___x_812_; lean_object* v_buckets_x27_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_inc(v_bkt_793_);
v___x_812_ = lean_box(0);
v_buckets_x27_813_ = lean_array_uset(v_buckets_776_, v___x_792_, v___x_812_);
v___x_814_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_773_, v_b_774_, v_bkt_793_);
v___x_815_ = lean_array_uset(v_buckets_x27_813_, v___x_792_, v___x_814_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_815_);
v___x_817_ = v___x_778_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_size_775_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_820_, lean_object* v_e_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_824_ = lean_st_ref_take(v_a_820_);
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_824_, v_e_821_, v_a_822_);
v___x_826_ = lean_st_ref_put(v_a_820_, v___x_825_);
v___x_827_ = lean_box(0);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_828_, lean_object* v_e_829_, lean_object* v_a_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_828_, v_e_829_, v_a_830_);
lean_dec(v_a_828_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_836_, lean_object* v_pre_837_, lean_object* v_post_838_, uint8_t v_usedLetOnly_839_, uint8_t v_skipConstInApp_840_, uint8_t v_skipInstances_841_, lean_object* v_body_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_array_push(v_fvars_836_, v_x_843_);
v___x_851_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_837_, v_post_838_, v_usedLetOnly_839_, v_skipConstInApp_840_, v_skipInstances_841_, v___x_850_, v_body_842_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_852_, lean_object* v_pre_853_, lean_object* v_post_854_, lean_object* v_usedLetOnly_855_, lean_object* v_skipConstInApp_856_, lean_object* v_skipInstances_857_, lean_object* v_body_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v_usedLetOnly_boxed_866_; uint8_t v_skipConstInApp_boxed_867_; uint8_t v_skipInstances_boxed_868_; lean_object* v_res_869_; 
v_usedLetOnly_boxed_866_ = lean_unbox(v_usedLetOnly_855_);
v_skipConstInApp_boxed_867_ = lean_unbox(v_skipConstInApp_856_);
v_skipInstances_boxed_868_ = lean_unbox(v_skipInstances_857_);
v_res_869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_852_, v_pre_853_, v_post_854_, v_usedLetOnly_boxed_866_, v_skipConstInApp_boxed_867_, v_skipInstances_boxed_868_, v_body_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_870_, lean_object* v_post_871_, uint8_t v_usedLetOnly_872_, uint8_t v_skipConstInApp_873_, uint8_t v_skipInstances_874_, lean_object* v_e_875_, lean_object* v_a_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
lean_inc_ref(v_post_871_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc_ref(v_e_875_);
v___x_882_ = lean_apply_6(v_post_871_, v_e_875_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_901_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_901_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_901_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_901_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
switch(lean_obj_tag(v_a_883_))
{
case 0:
{
lean_object* v_e_887_; lean_object* v___x_889_; 
lean_dec_ref(v_e_875_);
lean_dec_ref(v_post_871_);
lean_dec_ref(v_pre_870_);
v_e_887_ = lean_ctor_get(v_a_883_, 0);
lean_inc_ref(v_e_887_);
lean_dec_ref_known(v_a_883_, 1);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_e_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_e_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
case 1:
{
lean_object* v_e_891_; lean_object* v___x_892_; 
lean_del_object(v___x_885_);
lean_dec_ref(v_e_875_);
v_e_891_ = lean_ctor_get(v_a_883_, 0);
lean_inc_ref(v_e_891_);
lean_dec_ref_known(v_a_883_, 1);
v___x_892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_870_, v_post_871_, v_usedLetOnly_872_, v_skipConstInApp_873_, v_skipInstances_874_, v_e_891_, v_a_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_892_;
}
default: 
{
lean_object* v_e_x3f_893_; 
lean_dec_ref(v_post_871_);
lean_dec_ref(v_pre_870_);
v_e_x3f_893_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_e_x3f_893_);
lean_dec_ref_known(v_a_883_, 1);
if (lean_obj_tag(v_e_x3f_893_) == 0)
{
lean_object* v___x_895_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_e_875_);
v___x_895_ = v___x_885_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_e_875_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v_val_897_; lean_object* v___x_899_; 
lean_dec_ref(v_e_875_);
v_val_897_ = lean_ctor_get(v_e_x3f_893_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v_e_x3f_893_, 1);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_val_897_);
v___x_899_ = v___x_885_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_val_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_e_875_);
lean_dec_ref(v_post_871_);
lean_dec_ref(v_pre_870_);
v_a_902_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_882_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_882_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_910_, lean_object* v_post_911_, uint8_t v_usedLetOnly_912_, uint8_t v_skipConstInApp_913_, uint8_t v_skipInstances_914_, lean_object* v_fvars_915_, lean_object* v_e_916_, lean_object* v_a_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
if (lean_obj_tag(v_e_916_) == 6)
{
lean_object* v_binderName_923_; lean_object* v_binderType_924_; lean_object* v_body_925_; uint8_t v_binderInfo_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_binderName_923_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_binderName_923_);
v_binderType_924_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_binderType_924_);
v_body_925_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_body_925_);
v_binderInfo_926_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_916_, 3);
v___x_927_ = lean_expr_instantiate_rev(v_binderType_924_, v_fvars_915_);
lean_dec_ref(v_binderType_924_);
lean_inc_ref(v_post_911_);
lean_inc_ref(v_pre_910_);
v___x_928_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_910_, v_post_911_, v_usedLetOnly_912_, v_skipConstInApp_913_, v_skipInstances_914_, v___x_927_, v_a_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___f_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = lean_box(v_usedLetOnly_912_);
v___x_931_ = lean_box(v_skipConstInApp_913_);
v___x_932_ = lean_box(v_skipInstances_914_);
v___f_933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_933_, 0, v_fvars_915_);
lean_closure_set(v___f_933_, 1, v_pre_910_);
lean_closure_set(v___f_933_, 2, v_post_911_);
lean_closure_set(v___f_933_, 3, v___x_930_);
lean_closure_set(v___f_933_, 4, v___x_931_);
lean_closure_set(v___f_933_, 5, v___x_932_);
lean_closure_set(v___f_933_, 6, v_body_925_);
v___x_934_ = 0;
v___x_935_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_923_, v_binderInfo_926_, v_a_929_, v___f_933_, v___x_934_, v_a_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_935_;
}
else
{
lean_dec_ref(v_body_925_);
lean_dec(v_binderName_923_);
lean_dec_ref(v_fvars_915_);
lean_dec_ref(v_post_911_);
lean_dec_ref(v_pre_910_);
return v___x_928_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_expr_instantiate_rev(v_e_916_, v_fvars_915_);
lean_dec_ref(v_e_916_);
lean_inc_ref(v_post_911_);
lean_inc_ref(v_pre_910_);
v___x_937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_910_, v_post_911_, v_usedLetOnly_912_, v_skipConstInApp_913_, v_skipInstances_914_, v___x_936_, v_a_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; uint8_t v___x_939_; uint8_t v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = 0;
v___x_940_ = 1;
v___x_941_ = 1;
v___x_942_ = l_Lean_Meta_mkLambdaFVars(v_fvars_915_, v_a_938_, v___x_939_, v_usedLetOnly_912_, v___x_939_, v___x_940_, v___x_941_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec_ref(v_fvars_915_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_944_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_910_, v_post_911_, v_usedLetOnly_912_, v_skipConstInApp_913_, v_skipInstances_914_, v_a_943_, v_a_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_944_;
}
else
{
lean_dec_ref(v_post_911_);
lean_dec_ref(v_pre_910_);
return v___x_942_;
}
}
else
{
lean_dec_ref(v_fvars_915_);
lean_dec_ref(v_post_911_);
lean_dec_ref(v_pre_910_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_945_, lean_object* v_pre_946_, lean_object* v_post_947_, uint8_t v_usedLetOnly_948_, uint8_t v_skipConstInApp_949_, uint8_t v_skipInstances_950_, lean_object* v_body_951_, lean_object* v_x_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_array_push(v_fvars_945_, v_x_952_);
v___x_960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_946_, v_post_947_, v_usedLetOnly_948_, v_skipConstInApp_949_, v_skipInstances_950_, v___x_959_, v_body_951_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_961_, lean_object* v_pre_962_, lean_object* v_post_963_, lean_object* v_usedLetOnly_964_, lean_object* v_skipConstInApp_965_, lean_object* v_skipInstances_966_, lean_object* v_body_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v_usedLetOnly_boxed_975_; uint8_t v_skipConstInApp_boxed_976_; uint8_t v_skipInstances_boxed_977_; lean_object* v_res_978_; 
v_usedLetOnly_boxed_975_ = lean_unbox(v_usedLetOnly_964_);
v_skipConstInApp_boxed_976_ = lean_unbox(v_skipConstInApp_965_);
v_skipInstances_boxed_977_ = lean_unbox(v_skipInstances_966_);
v_res_978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_961_, v_pre_962_, v_post_963_, v_usedLetOnly_boxed_975_, v_skipConstInApp_boxed_976_, v_skipInstances_boxed_977_, v_body_967_, v_x_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_979_, lean_object* v_post_980_, uint8_t v_usedLetOnly_981_, uint8_t v_skipConstInApp_982_, uint8_t v_skipInstances_983_, lean_object* v_fvars_984_, lean_object* v_e_985_, lean_object* v_a_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
if (lean_obj_tag(v_e_985_) == 8)
{
lean_object* v_declName_992_; lean_object* v_type_993_; lean_object* v_value_994_; lean_object* v_body_995_; uint8_t v_nondep_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_declName_992_ = lean_ctor_get(v_e_985_, 0);
lean_inc(v_declName_992_);
v_type_993_ = lean_ctor_get(v_e_985_, 1);
lean_inc_ref(v_type_993_);
v_value_994_ = lean_ctor_get(v_e_985_, 2);
lean_inc_ref(v_value_994_);
v_body_995_ = lean_ctor_get(v_e_985_, 3);
lean_inc_ref(v_body_995_);
v_nondep_996_ = lean_ctor_get_uint8(v_e_985_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_985_, 4);
v___x_997_ = lean_expr_instantiate_rev(v_type_993_, v_fvars_984_);
lean_dec_ref(v_type_993_);
lean_inc_ref(v_post_980_);
lean_inc_ref(v_pre_979_);
v___x_998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_979_, v_post_980_, v_usedLetOnly_981_, v_skipConstInApp_982_, v_skipInstances_983_, v___x_997_, v_a_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = lean_expr_instantiate_rev(v_value_994_, v_fvars_984_);
lean_dec_ref(v_value_994_);
lean_inc_ref(v_post_980_);
lean_inc_ref(v_pre_979_);
v___x_1001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_979_, v_post_980_, v_usedLetOnly_981_, v_skipConstInApp_982_, v_skipInstances_983_, v___x_1000_, v_a_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = lean_box(v_usedLetOnly_981_);
v___x_1004_ = lean_box(v_skipConstInApp_982_);
v___x_1005_ = lean_box(v_skipInstances_983_);
v___f_1006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1006_, 0, v_fvars_984_);
lean_closure_set(v___f_1006_, 1, v_pre_979_);
lean_closure_set(v___f_1006_, 2, v_post_980_);
lean_closure_set(v___f_1006_, 3, v___x_1003_);
lean_closure_set(v___f_1006_, 4, v___x_1004_);
lean_closure_set(v___f_1006_, 5, v___x_1005_);
lean_closure_set(v___f_1006_, 6, v_body_995_);
v___x_1007_ = 0;
v___x_1008_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_992_, v_a_999_, v_a_1002_, v___f_1006_, v_nondep_996_, v___x_1007_, v_a_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_1008_;
}
else
{
lean_dec(v_a_999_);
lean_dec_ref(v_body_995_);
lean_dec(v_declName_992_);
lean_dec_ref(v_fvars_984_);
lean_dec_ref(v_post_980_);
lean_dec_ref(v_pre_979_);
return v___x_1001_;
}
}
else
{
lean_dec_ref(v_body_995_);
lean_dec_ref(v_value_994_);
lean_dec(v_declName_992_);
lean_dec_ref(v_fvars_984_);
lean_dec_ref(v_post_980_);
lean_dec_ref(v_pre_979_);
return v___x_998_;
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_expr_instantiate_rev(v_e_985_, v_fvars_984_);
lean_dec_ref(v_e_985_);
lean_inc_ref(v_post_980_);
lean_inc_ref(v_pre_979_);
v___x_1010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_979_, v_post_980_, v_usedLetOnly_981_, v_skipConstInApp_982_, v_skipInstances_983_, v___x_1009_, v_a_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; uint8_t v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = 0;
v___x_1013_ = 1;
v___x_1014_ = l_Lean_Meta_mkLetFVars(v_fvars_984_, v_a_1011_, v_usedLetOnly_981_, v___x_1012_, v___x_1013_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec_ref(v_fvars_984_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_979_, v_post_980_, v_usedLetOnly_981_, v_skipConstInApp_982_, v_skipInstances_983_, v_a_1015_, v_a_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_1016_;
}
else
{
lean_dec_ref(v_post_980_);
lean_dec_ref(v_pre_979_);
return v___x_1014_;
}
}
else
{
lean_dec_ref(v_fvars_984_);
lean_dec_ref(v_post_980_);
lean_dec_ref(v_pre_979_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1017_, lean_object* v_post_1018_, uint8_t v_usedLetOnly_1019_, uint8_t v_skipConstInApp_1020_, uint8_t v_skipInstances_1021_, size_t v_sz_1022_, size_t v_i_1023_, lean_object* v_bs_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_usize_dec_lt(v_i_1023_, v_sz_1022_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_dec_ref(v_post_1018_);
lean_dec_ref(v_pre_1017_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_bs_1024_);
return v___x_1032_;
}
else
{
lean_object* v_v_1033_; lean_object* v___x_1034_; 
v_v_1033_ = lean_array_uget_borrowed(v_bs_1024_, v_i_1023_);
lean_inc(v_v_1033_);
lean_inc_ref(v_post_1018_);
lean_inc_ref(v_pre_1017_);
v___x_1034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1017_, v_post_1018_, v_usedLetOnly_1019_, v_skipConstInApp_1020_, v_skipInstances_1021_, v_v_1033_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v_bs_x27_1037_; size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = lean_unsigned_to_nat(0u);
v_bs_x27_1037_ = lean_array_uset(v_bs_1024_, v_i_1023_, v___x_1036_);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_add(v_i_1023_, v___x_1038_);
v___x_1040_ = lean_array_uset(v_bs_x27_1037_, v_i_1023_, v_a_1035_);
v_i_1023_ = v___x_1039_;
v_bs_1024_ = v___x_1040_;
goto _start;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_bs_1024_);
lean_dec_ref(v_post_1018_);
lean_dec_ref(v_pre_1017_);
v_a_1042_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1034_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1034_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1050_, lean_object* v_post_1051_, uint8_t v_usedLetOnly_1052_, uint8_t v_skipConstInApp_1053_, uint8_t v_skipInstances_1054_, lean_object* v___x_1055_, lean_object* v___y_1056_, lean_object* v_b_1057_, lean_object* v_a_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1050_, v_post_1051_, v_usedLetOnly_1052_, v_skipConstInApp_1053_, v_skipInstances_1054_, v___x_1055_, v___y_1056_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1074_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1069_ = lean_array_fset(v_b_1057_, v_a_1058_, v_a_1065_);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1070_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_b_1057_);
v_a_1075_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1064_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1064_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1083_, lean_object* v_post_1084_, lean_object* v_usedLetOnly_1085_, lean_object* v_skipConstInApp_1086_, lean_object* v_skipInstances_1087_, lean_object* v___x_1088_, lean_object* v___y_1089_, lean_object* v_b_1090_, lean_object* v_a_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint8_t v_usedLetOnly_boxed_1097_; uint8_t v_skipConstInApp_boxed_1098_; uint8_t v_skipInstances_boxed_1099_; lean_object* v_res_1100_; 
v_usedLetOnly_boxed_1097_ = lean_unbox(v_usedLetOnly_1085_);
v_skipConstInApp_boxed_1098_ = lean_unbox(v_skipConstInApp_1086_);
v_skipInstances_boxed_1099_ = lean_unbox(v_skipInstances_1087_);
v_res_1100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1083_, v_post_1084_, v_usedLetOnly_boxed_1097_, v_skipConstInApp_boxed_1098_, v_skipInstances_boxed_1099_, v___x_1088_, v___y_1089_, v_b_1090_, v_a_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_a_1091_);
lean_dec(v___y_1089_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1101_, lean_object* v___x_1102_, lean_object* v_pre_1103_, lean_object* v_post_1104_, uint8_t v_usedLetOnly_1105_, uint8_t v_skipConstInApp_1106_, uint8_t v_skipInstances_1107_, lean_object* v_a_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___y_1117_; uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_lt(v_a_1108_, v_upperBound_1101_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v_a_1108_);
lean_dec_ref(v_post_1104_);
lean_dec_ref(v_pre_1103_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_b_1109_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_array_fget_borrowed(v_b_1109_, v_a_1108_);
v___x_1143_ = lean_array_get_size(v___x_1102_);
v___x_1144_ = lean_nat_dec_lt(v_a_1108_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; 
lean_inc(v___x_1142_);
v___x_1145_ = lean_box(v_usedLetOnly_1105_);
v___x_1146_ = lean_box(v_skipConstInApp_1106_);
v___x_1147_ = lean_box(v_skipInstances_1107_);
lean_inc(v_a_1108_);
lean_inc(v___y_1110_);
lean_inc_ref(v_post_1104_);
lean_inc_ref(v_pre_1103_);
v___f_1148_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1148_, 0, v_pre_1103_);
lean_closure_set(v___f_1148_, 1, v_post_1104_);
lean_closure_set(v___f_1148_, 2, v___x_1145_);
lean_closure_set(v___f_1148_, 3, v___x_1146_);
lean_closure_set(v___f_1148_, 4, v___x_1147_);
lean_closure_set(v___f_1148_, 5, v___x_1142_);
lean_closure_set(v___f_1148_, 6, v___y_1110_);
lean_closure_set(v___f_1148_, 7, v_b_1109_);
lean_closure_set(v___f_1148_, 8, v_a_1108_);
v___y_1117_ = v___f_1148_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1149_; uint8_t v_isInstance_1150_; 
v___x_1149_ = lean_array_fget_borrowed(v___x_1102_, v_a_1108_);
v_isInstance_1150_ = lean_ctor_get_uint8(v___x_1149_, sizeof(void*)*1 + 4);
if (v_isInstance_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___f_1154_; 
lean_inc(v___x_1142_);
v___x_1151_ = lean_box(v_usedLetOnly_1105_);
v___x_1152_ = lean_box(v_skipConstInApp_1106_);
v___x_1153_ = lean_box(v_skipInstances_1107_);
lean_inc(v_a_1108_);
lean_inc(v___y_1110_);
lean_inc_ref(v_post_1104_);
lean_inc_ref(v_pre_1103_);
v___f_1154_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1154_, 0, v_pre_1103_);
lean_closure_set(v___f_1154_, 1, v_post_1104_);
lean_closure_set(v___f_1154_, 2, v___x_1151_);
lean_closure_set(v___f_1154_, 3, v___x_1152_);
lean_closure_set(v___f_1154_, 4, v___x_1153_);
lean_closure_set(v___f_1154_, 5, v___x_1142_);
lean_closure_set(v___f_1154_, 6, v___y_1110_);
lean_closure_set(v___f_1154_, 7, v_b_1109_);
lean_closure_set(v___f_1154_, 8, v_a_1108_);
v___y_1117_ = v___f_1154_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1155_; lean_object* v___f_1156_; 
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_b_1109_);
v___f_1156_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1156_, 0, v___x_1155_);
v___y_1117_ = v___f_1156_;
goto v___jp_1116_;
}
}
}
v___jp_1116_:
{
lean_object* v___x_1118_; 
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1113_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
v___x_1118_ = lean_apply_5(v___y_1117_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1131_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1131_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1131_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
if (lean_obj_tag(v_a_1119_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; 
lean_dec(v_a_1108_);
lean_dec_ref(v_post_1104_);
lean_dec_ref(v_pre_1103_);
v_a_1123_ = lean_ctor_get(v_a_1119_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v_a_1119_, 1);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v_a_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1121_);
v_a_1127_ = lean_ctor_get(v_a_1119_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v_a_1119_, 1);
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_a_1108_, v___x_1128_);
lean_dec(v_a_1108_);
v_a_1108_ = v___x_1129_;
v_b_1109_ = v_a_1127_;
goto _start;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_a_1108_);
lean_dec_ref(v_post_1104_);
lean_dec_ref(v_pre_1103_);
v_a_1132_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1118_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1118_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1157_, lean_object* v_pre_1158_, lean_object* v_post_1159_, uint8_t v_usedLetOnly_1160_, uint8_t v_skipConstInApp_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_f_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; 
if (lean_obj_tag(v_x_1162_) == 5)
{
lean_object* v_fn_1220_; lean_object* v_arg_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_fn_1220_ = lean_ctor_get(v_x_1162_, 0);
lean_inc_ref(v_fn_1220_);
v_arg_1221_ = lean_ctor_get(v_x_1162_, 1);
lean_inc_ref(v_arg_1221_);
lean_dec_ref_known(v_x_1162_, 2);
v___x_1222_ = lean_array_set(v_x_1163_, v_x_1164_, v_arg_1221_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_sub(v_x_1164_, v___x_1223_);
lean_dec(v_x_1164_);
v_x_1162_ = v_fn_1220_;
v_x_1163_ = v___x_1222_;
v_x_1164_ = v___x_1224_;
goto _start;
}
else
{
lean_dec(v_x_1164_);
if (v_skipConstInApp_1161_ == 0)
{
goto v___jp_1217_;
}
else
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Lean_Expr_isConst(v_x_1162_);
if (v___x_1226_ == 0)
{
goto v___jp_1217_;
}
else
{
v_f_1172_ = v_x_1162_;
v___y_1173_ = v___y_1165_;
v___y_1174_ = v___y_1166_;
v___y_1175_ = v___y_1167_;
v___y_1176_ = v___y_1168_;
v___y_1177_ = v___y_1169_;
goto v___jp_1171_;
}
}
}
v___jp_1171_:
{
if (v_skipInstances_1157_ == 0)
{
size_t v_sz_1178_; size_t v___x_1179_; lean_object* v___x_1180_; 
v_sz_1178_ = lean_array_size(v_x_1163_);
v___x_1179_ = ((size_t)0ULL);
lean_inc_ref(v_post_1159_);
lean_inc_ref(v_pre_1158_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1158_, v_post_1159_, v_usedLetOnly_1160_, v_skipConstInApp_1161_, v_skipInstances_1157_, v_sz_1178_, v___x_1179_, v_x_1163_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = l_Lean_mkAppN(v_f_1172_, v_a_1181_);
lean_dec(v_a_1181_);
v___x_1183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1158_, v_post_1159_, v_usedLetOnly_1160_, v_skipConstInApp_1161_, v_skipInstances_1157_, v___x_1182_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1183_;
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_f_1172_);
lean_dec_ref(v_post_1159_);
lean_dec_ref(v_pre_1158_);
v_a_1184_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1180_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1180_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_array_get_size(v_x_1163_);
lean_inc_ref(v_f_1172_);
v___x_1193_ = l_Lean_Meta_getFunInfoNArgs(v_f_1172_, v___x_1192_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v_paramInfo_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v_paramInfo_1195_ = lean_ctor_get(v_a_1194_, 0);
lean_inc_ref(v_paramInfo_1195_);
lean_dec(v_a_1194_);
v___x_1196_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1159_);
lean_inc_ref(v_pre_1158_);
v___x_1197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1192_, v_paramInfo_1195_, v_pre_1158_, v_post_1159_, v_usedLetOnly_1160_, v_skipConstInApp_1161_, v_skipInstances_1157_, v___x_1196_, v_x_1163_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec_ref(v_paramInfo_1195_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = l_Lean_mkAppN(v_f_1172_, v_a_1198_);
lean_dec(v_a_1198_);
v___x_1200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1158_, v_post_1159_, v_usedLetOnly_1160_, v_skipConstInApp_1161_, v_skipInstances_1157_, v___x_1199_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1200_;
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_f_1172_);
lean_dec_ref(v_post_1159_);
lean_dec_ref(v_pre_1158_);
v_a_1201_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1197_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1197_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_f_1172_);
lean_dec_ref(v_x_1163_);
lean_dec_ref(v_post_1159_);
lean_dec_ref(v_pre_1158_);
v_a_1209_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1193_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1193_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
v___jp_1217_:
{
lean_object* v___x_1218_; 
lean_inc_ref(v_post_1159_);
lean_inc_ref(v_pre_1158_);
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1158_, v_post_1159_, v_usedLetOnly_1160_, v_skipConstInApp_1161_, v_skipInstances_1157_, v_x_1162_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_f_1172_ = v_a_1219_;
v___y_1173_ = v___y_1165_;
v___y_1174_ = v___y_1166_;
v___y_1175_ = v___y_1167_;
v___y_1176_ = v___y_1168_;
v___y_1177_ = v___y_1169_;
goto v___jp_1171_;
}
else
{
lean_dec_ref(v_x_1163_);
lean_dec_ref(v_post_1159_);
lean_dec_ref(v_pre_1158_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1227_, lean_object* v_pre_1228_, lean_object* v_e_1229_, lean_object* v_post_1230_, uint8_t v_usedLetOnly_1231_, uint8_t v_skipConstInApp_1232_, uint8_t v_skipInstances_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Core_checkSystem(v___x_1227_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1240_, 1);
lean_inc_ref(v_pre_1228_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc_ref(v_e_1229_);
v___x_1241_ = lean_apply_6(v_pre_1228_, v_e_1229_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, lean_box(0));
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1290_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1290_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1290_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___y_1247_; 
switch(lean_obj_tag(v_a_1242_))
{
case 0:
{
lean_object* v_e_1282_; lean_object* v___x_1284_; 
lean_dec_ref(v_post_1230_);
lean_dec_ref(v_e_1229_);
lean_dec_ref(v_pre_1228_);
v_e_1282_ = lean_ctor_get(v_a_1242_, 0);
lean_inc_ref(v_e_1282_);
lean_dec_ref_known(v_a_1242_, 1);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_e_1282_);
v___x_1284_ = v___x_1244_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_e_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
case 1:
{
lean_object* v_e_1286_; lean_object* v___x_1287_; 
lean_del_object(v___x_1244_);
lean_dec_ref(v_e_1229_);
v_e_1286_ = lean_ctor_get(v_a_1242_, 0);
lean_inc_ref(v_e_1286_);
lean_dec_ref_known(v_a_1242_, 1);
v___x_1287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v_e_1286_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1287_;
}
default: 
{
lean_object* v_e_x3f_1288_; 
lean_del_object(v___x_1244_);
v_e_x3f_1288_ = lean_ctor_get(v_a_1242_, 0);
lean_inc(v_e_x3f_1288_);
lean_dec_ref_known(v_a_1242_, 1);
if (lean_obj_tag(v_e_x3f_1288_) == 0)
{
v___y_1247_ = v_e_1229_;
goto v___jp_1246_;
}
else
{
lean_object* v_val_1289_; 
lean_dec_ref(v_e_1229_);
v_val_1289_ = lean_ctor_get(v_e_x3f_1288_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v_e_x3f_1288_, 1);
v___y_1247_ = v_val_1289_;
goto v___jp_1246_;
}
}
}
v___jp_1246_:
{
switch(lean_obj_tag(v___y_1247_))
{
case 7:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___x_1248_, v___y_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1249_;
}
case 6:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___x_1250_, v___y_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1251_;
}
case 8:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___x_1252_, v___y_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1253_;
}
case 5:
{
lean_object* v_dummy_1254_; lean_object* v_nargs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_dummy_1254_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1255_ = l_Lean_Expr_getAppNumArgs(v___y_1247_);
lean_inc(v_nargs_1255_);
v___x_1256_ = lean_mk_array(v_nargs_1255_, v_dummy_1254_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_sub(v_nargs_1255_, v___x_1257_);
lean_dec(v_nargs_1255_);
v___x_1259_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1233_, v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v___y_1247_, v___x_1256_, v___x_1258_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1259_;
}
case 10:
{
lean_object* v_data_1260_; lean_object* v_expr_1261_; lean_object* v___x_1262_; 
v_data_1260_ = lean_ctor_get(v___y_1247_, 0);
v_expr_1261_ = lean_ctor_get(v___y_1247_, 1);
lean_inc_ref(v_expr_1261_);
lean_inc_ref(v_post_1230_);
lean_inc_ref(v_pre_1228_);
v___x_1262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v_expr_1261_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; size_t v___x_1264_; size_t v___x_1265_; uint8_t v___x_1266_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_ptr_addr(v_expr_1261_);
v___x_1265_ = lean_ptr_addr(v_a_1263_);
v___x_1266_ = lean_usize_dec_eq(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_inc(v_data_1260_);
lean_dec_ref_known(v___y_1247_, 2);
v___x_1267_ = l_Lean_Expr_mdata___override(v_data_1260_, v_a_1263_);
v___x_1268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___x_1267_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_a_1263_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___y_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1269_;
}
}
else
{
lean_dec_ref_known(v___y_1247_, 2);
lean_dec_ref(v_post_1230_);
lean_dec_ref(v_pre_1228_);
return v___x_1262_;
}
}
case 11:
{
lean_object* v_typeName_1270_; lean_object* v_idx_1271_; lean_object* v_struct_1272_; lean_object* v___x_1273_; 
v_typeName_1270_ = lean_ctor_get(v___y_1247_, 0);
v_idx_1271_ = lean_ctor_get(v___y_1247_, 1);
v_struct_1272_ = lean_ctor_get(v___y_1247_, 2);
lean_inc_ref(v_struct_1272_);
lean_inc_ref(v_post_1230_);
lean_inc_ref(v_pre_1228_);
v___x_1273_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v_struct_1272_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; size_t v___x_1275_; size_t v___x_1276_; uint8_t v___x_1277_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = lean_ptr_addr(v_struct_1272_);
v___x_1276_ = lean_ptr_addr(v_a_1274_);
v___x_1277_ = lean_usize_dec_eq(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_inc(v_idx_1271_);
lean_inc(v_typeName_1270_);
lean_dec_ref_known(v___y_1247_, 3);
v___x_1278_ = l_Lean_Expr_proj___override(v_typeName_1270_, v_idx_1271_, v_a_1274_);
v___x_1279_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___x_1278_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; 
lean_dec(v_a_1274_);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___y_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1280_;
}
}
else
{
lean_dec_ref_known(v___y_1247_, 3);
lean_dec_ref(v_post_1230_);
lean_dec_ref(v_pre_1228_);
return v___x_1273_;
}
}
default: 
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1228_, v_post_1230_, v_usedLetOnly_1231_, v_skipConstInApp_1232_, v_skipInstances_1233_, v___y_1247_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_post_1230_);
lean_dec_ref(v_e_1229_);
lean_dec_ref(v_pre_1228_);
v_a_1291_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1241_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1241_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_post_1230_);
lean_dec_ref(v_e_1229_);
lean_dec_ref(v_pre_1228_);
v_a_1299_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1240_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1240_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1307_, lean_object* v_pre_1308_, lean_object* v_e_1309_, lean_object* v_post_1310_, lean_object* v_usedLetOnly_1311_, lean_object* v_skipConstInApp_1312_, lean_object* v_skipInstances_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v_usedLetOnly_boxed_1320_; uint8_t v_skipConstInApp_boxed_1321_; uint8_t v_skipInstances_boxed_1322_; lean_object* v_res_1323_; 
v_usedLetOnly_boxed_1320_ = lean_unbox(v_usedLetOnly_1311_);
v_skipConstInApp_boxed_1321_ = lean_unbox(v_skipConstInApp_1312_);
v_skipInstances_boxed_1322_ = lean_unbox(v_skipInstances_1313_);
v_res_1323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1307_, v_pre_1308_, v_e_1309_, v_post_1310_, v_usedLetOnly_boxed_1320_, v_skipConstInApp_boxed_1321_, v_skipInstances_boxed_1322_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1324_, lean_object* v_post_1325_, uint8_t v_usedLetOnly_1326_, uint8_t v_skipConstInApp_1327_, uint8_t v_skipInstances_1328_, lean_object* v_e_1329_, lean_object* v_a_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_inc(v_a_1330_);
v___x_1336_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1336_, 0, lean_box(0));
lean_closure_set(v___x_1336_, 1, lean_box(0));
lean_closure_set(v___x_1336_, 2, v_a_1330_);
v___x_1337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1336_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1372_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1372_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1372_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1338_, v_e_1329_);
lean_dec(v_a_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
lean_del_object(v___x_1340_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1344_ = lean_box(v_usedLetOnly_1326_);
v___x_1345_ = lean_box(v_skipConstInApp_1327_);
v___x_1346_ = lean_box(v_skipInstances_1328_);
lean_inc_ref(v_e_1329_);
v___f_1347_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1347_, 0, v___x_1343_);
lean_closure_set(v___f_1347_, 1, v_pre_1324_);
lean_closure_set(v___f_1347_, 2, v_e_1329_);
lean_closure_set(v___f_1347_, 3, v_post_1325_);
lean_closure_set(v___f_1347_, 4, v___x_1344_);
lean_closure_set(v___f_1347_, 5, v___x_1345_);
lean_closure_set(v___f_1347_, 6, v___x_1346_);
v___x_1348_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1347_, v_a_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___f_1350_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_n(v_a_1349_, 2);
lean_dec_ref_known(v___x_1348_, 1);
lean_inc(v_a_1330_);
v___f_1350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1350_, 0, v_a_1330_);
lean_closure_set(v___f_1350_, 1, v_e_1329_);
lean_closure_set(v___f_1350_, 2, v_a_1349_);
v___x_1351_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1350_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v___x_1351_, 0);
lean_dec(v_unused_1359_);
v___x_1353_ = v___x_1351_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v___x_1351_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_a_1349_);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1349_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1349_);
v_a_1360_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1351_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1351_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_dec_ref(v_e_1329_);
return v___x_1348_;
}
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1370_; 
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_post_1325_);
lean_dec_ref(v_pre_1324_);
v_val_1368_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v___x_1342_, 1);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_val_1368_);
v___x_1370_ = v___x_1340_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_val_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_post_1325_);
lean_dec_ref(v_pre_1324_);
v_a_1373_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1337_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1337_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1381_, lean_object* v_pre_1382_, lean_object* v_post_1383_, lean_object* v_usedLetOnly_1384_, lean_object* v_skipConstInApp_1385_, lean_object* v_skipInstances_1386_, lean_object* v_body_1387_, lean_object* v_x_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_usedLetOnly_boxed_1395_; uint8_t v_skipConstInApp_boxed_1396_; uint8_t v_skipInstances_boxed_1397_; lean_object* v_res_1398_; 
v_usedLetOnly_boxed_1395_ = lean_unbox(v_usedLetOnly_1384_);
v_skipConstInApp_boxed_1396_ = lean_unbox(v_skipConstInApp_1385_);
v_skipInstances_boxed_1397_ = lean_unbox(v_skipInstances_1386_);
v_res_1398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1381_, v_pre_1382_, v_post_1383_, v_usedLetOnly_boxed_1395_, v_skipConstInApp_boxed_1396_, v_skipInstances_boxed_1397_, v_body_1387_, v_x_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1399_, lean_object* v_post_1400_, uint8_t v_usedLetOnly_1401_, uint8_t v_skipConstInApp_1402_, uint8_t v_skipInstances_1403_, lean_object* v_fvars_1404_, lean_object* v_e_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
if (lean_obj_tag(v_e_1405_) == 7)
{
lean_object* v_binderName_1412_; lean_object* v_binderType_1413_; lean_object* v_body_1414_; uint8_t v_binderInfo_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_binderName_1412_ = lean_ctor_get(v_e_1405_, 0);
lean_inc(v_binderName_1412_);
v_binderType_1413_ = lean_ctor_get(v_e_1405_, 1);
lean_inc_ref(v_binderType_1413_);
v_body_1414_ = lean_ctor_get(v_e_1405_, 2);
lean_inc_ref(v_body_1414_);
v_binderInfo_1415_ = lean_ctor_get_uint8(v_e_1405_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1405_, 3);
v___x_1416_ = lean_expr_instantiate_rev(v_binderType_1413_, v_fvars_1404_);
lean_dec_ref(v_binderType_1413_);
lean_inc_ref(v_post_1400_);
lean_inc_ref(v_pre_1399_);
v___x_1417_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1399_, v_post_1400_, v_usedLetOnly_1401_, v_skipConstInApp_1402_, v_skipInstances_1403_, v___x_1416_, v_a_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = lean_box(v_usedLetOnly_1401_);
v___x_1420_ = lean_box(v_skipConstInApp_1402_);
v___x_1421_ = lean_box(v_skipInstances_1403_);
v___f_1422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1422_, 0, v_fvars_1404_);
lean_closure_set(v___f_1422_, 1, v_pre_1399_);
lean_closure_set(v___f_1422_, 2, v_post_1400_);
lean_closure_set(v___f_1422_, 3, v___x_1419_);
lean_closure_set(v___f_1422_, 4, v___x_1420_);
lean_closure_set(v___f_1422_, 5, v___x_1421_);
lean_closure_set(v___f_1422_, 6, v_body_1414_);
v___x_1423_ = 0;
v___x_1424_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1412_, v_binderInfo_1415_, v_a_1418_, v___f_1422_, v___x_1423_, v_a_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1424_;
}
else
{
lean_dec_ref(v_body_1414_);
lean_dec(v_binderName_1412_);
lean_dec_ref(v_fvars_1404_);
lean_dec_ref(v_post_1400_);
lean_dec_ref(v_pre_1399_);
return v___x_1417_;
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_expr_instantiate_rev(v_e_1405_, v_fvars_1404_);
lean_dec_ref(v_e_1405_);
lean_inc_ref(v_post_1400_);
lean_inc_ref(v_pre_1399_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1399_, v_post_1400_, v_usedLetOnly_1401_, v_skipConstInApp_1402_, v_skipInstances_1403_, v___x_1425_, v_a_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; uint8_t v___x_1428_; uint8_t v___x_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = 0;
v___x_1429_ = 1;
v___x_1430_ = 1;
v___x_1431_ = l_Lean_Meta_mkForallFVars(v_fvars_1404_, v_a_1427_, v___x_1428_, v_usedLetOnly_1401_, v___x_1429_, v___x_1430_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec_ref(v_fvars_1404_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1399_, v_post_1400_, v_usedLetOnly_1401_, v_skipConstInApp_1402_, v_skipInstances_1403_, v_a_1432_, v_a_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1433_;
}
else
{
lean_dec_ref(v_post_1400_);
lean_dec_ref(v_pre_1399_);
return v___x_1431_;
}
}
else
{
lean_dec_ref(v_fvars_1404_);
lean_dec_ref(v_post_1400_);
lean_dec_ref(v_pre_1399_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1434_, lean_object* v_pre_1435_, lean_object* v_post_1436_, uint8_t v_usedLetOnly_1437_, uint8_t v_skipConstInApp_1438_, uint8_t v_skipInstances_1439_, lean_object* v_body_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_array_push(v_fvars_1434_, v_x_1441_);
v___x_1449_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1435_, v_post_1436_, v_usedLetOnly_1437_, v_skipConstInApp_1438_, v_skipInstances_1439_, v___x_1448_, v_body_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1450_, lean_object* v_post_1451_, lean_object* v_usedLetOnly_1452_, lean_object* v_skipConstInApp_1453_, lean_object* v_skipInstances_1454_, lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v_usedLetOnly_boxed_1462_; uint8_t v_skipConstInApp_boxed_1463_; uint8_t v_skipInstances_boxed_1464_; lean_object* v_res_1465_; 
v_usedLetOnly_boxed_1462_ = lean_unbox(v_usedLetOnly_1452_);
v_skipConstInApp_boxed_1463_ = lean_unbox(v_skipConstInApp_1453_);
v_skipInstances_boxed_1464_ = lean_unbox(v_skipInstances_1454_);
v_res_1465_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1450_, v_post_1451_, v_usedLetOnly_boxed_1462_, v_skipConstInApp_boxed_1463_, v_skipInstances_boxed_1464_, v_e_1455_, v_a_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v_a_1456_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1466_, lean_object* v_post_1467_, lean_object* v_usedLetOnly_1468_, lean_object* v_skipConstInApp_1469_, lean_object* v_skipInstances_1470_, lean_object* v_sz_1471_, lean_object* v_i_1472_, lean_object* v_bs_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v_usedLetOnly_boxed_1480_; uint8_t v_skipConstInApp_boxed_1481_; uint8_t v_skipInstances_boxed_1482_; size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_usedLetOnly_boxed_1480_ = lean_unbox(v_usedLetOnly_1468_);
v_skipConstInApp_boxed_1481_ = lean_unbox(v_skipConstInApp_1469_);
v_skipInstances_boxed_1482_ = lean_unbox(v_skipInstances_1470_);
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1471_);
lean_dec(v_sz_1471_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1466_, v_post_1467_, v_usedLetOnly_boxed_1480_, v_skipConstInApp_boxed_1481_, v_skipInstances_boxed_1482_, v_sz_boxed_1483_, v_i_boxed_1484_, v_bs_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1486_, lean_object* v_post_1487_, lean_object* v_usedLetOnly_1488_, lean_object* v_skipConstInApp_1489_, lean_object* v_skipInstances_1490_, lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_usedLetOnly_boxed_1498_; uint8_t v_skipConstInApp_boxed_1499_; uint8_t v_skipInstances_boxed_1500_; lean_object* v_res_1501_; 
v_usedLetOnly_boxed_1498_ = lean_unbox(v_usedLetOnly_1488_);
v_skipConstInApp_boxed_1499_ = lean_unbox(v_skipConstInApp_1489_);
v_skipInstances_boxed_1500_ = lean_unbox(v_skipInstances_1490_);
v_res_1501_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1486_, v_post_1487_, v_usedLetOnly_boxed_1498_, v_skipConstInApp_boxed_1499_, v_skipInstances_boxed_1500_, v_e_1491_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v_a_1492_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1502_, lean_object* v_post_1503_, lean_object* v_usedLetOnly_1504_, lean_object* v_skipConstInApp_1505_, lean_object* v_skipInstances_1506_, lean_object* v_fvars_1507_, lean_object* v_e_1508_, lean_object* v_a_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v_usedLetOnly_boxed_1515_; uint8_t v_skipConstInApp_boxed_1516_; uint8_t v_skipInstances_boxed_1517_; lean_object* v_res_1518_; 
v_usedLetOnly_boxed_1515_ = lean_unbox(v_usedLetOnly_1504_);
v_skipConstInApp_boxed_1516_ = lean_unbox(v_skipConstInApp_1505_);
v_skipInstances_boxed_1517_ = lean_unbox(v_skipInstances_1506_);
v_res_1518_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1502_, v_post_1503_, v_usedLetOnly_boxed_1515_, v_skipConstInApp_boxed_1516_, v_skipInstances_boxed_1517_, v_fvars_1507_, v_e_1508_, v_a_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v_a_1509_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1519_, lean_object* v_post_1520_, lean_object* v_usedLetOnly_1521_, lean_object* v_skipConstInApp_1522_, lean_object* v_skipInstances_1523_, lean_object* v_fvars_1524_, lean_object* v_e_1525_, lean_object* v_a_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_usedLetOnly_boxed_1532_; uint8_t v_skipConstInApp_boxed_1533_; uint8_t v_skipInstances_boxed_1534_; lean_object* v_res_1535_; 
v_usedLetOnly_boxed_1532_ = lean_unbox(v_usedLetOnly_1521_);
v_skipConstInApp_boxed_1533_ = lean_unbox(v_skipConstInApp_1522_);
v_skipInstances_boxed_1534_ = lean_unbox(v_skipInstances_1523_);
v_res_1535_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1519_, v_post_1520_, v_usedLetOnly_boxed_1532_, v_skipConstInApp_boxed_1533_, v_skipInstances_boxed_1534_, v_fvars_1524_, v_e_1525_, v_a_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v_a_1526_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1536_, lean_object* v_post_1537_, lean_object* v_usedLetOnly_1538_, lean_object* v_skipConstInApp_1539_, lean_object* v_skipInstances_1540_, lean_object* v_fvars_1541_, lean_object* v_e_1542_, lean_object* v_a_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v_usedLetOnly_boxed_1549_; uint8_t v_skipConstInApp_boxed_1550_; uint8_t v_skipInstances_boxed_1551_; lean_object* v_res_1552_; 
v_usedLetOnly_boxed_1549_ = lean_unbox(v_usedLetOnly_1538_);
v_skipConstInApp_boxed_1550_ = lean_unbox(v_skipConstInApp_1539_);
v_skipInstances_boxed_1551_ = lean_unbox(v_skipInstances_1540_);
v_res_1552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1536_, v_post_1537_, v_usedLetOnly_boxed_1549_, v_skipConstInApp_boxed_1550_, v_skipInstances_boxed_1551_, v_fvars_1541_, v_e_1542_, v_a_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v_a_1543_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1553_, lean_object* v___x_1554_, lean_object* v_pre_1555_, lean_object* v_post_1556_, lean_object* v_usedLetOnly_1557_, lean_object* v_skipConstInApp_1558_, lean_object* v_skipInstances_1559_, lean_object* v_a_1560_, lean_object* v_b_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_usedLetOnly_boxed_1568_; uint8_t v_skipConstInApp_boxed_1569_; uint8_t v_skipInstances_boxed_1570_; lean_object* v_res_1571_; 
v_usedLetOnly_boxed_1568_ = lean_unbox(v_usedLetOnly_1557_);
v_skipConstInApp_boxed_1569_ = lean_unbox(v_skipConstInApp_1558_);
v_skipInstances_boxed_1570_ = lean_unbox(v_skipInstances_1559_);
v_res_1571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1553_, v___x_1554_, v_pre_1555_, v_post_1556_, v_usedLetOnly_boxed_1568_, v_skipConstInApp_boxed_1569_, v_skipInstances_boxed_1570_, v_a_1560_, v_b_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___x_1554_);
lean_dec(v_upperBound_1553_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1572_, lean_object* v_pre_1573_, lean_object* v_post_1574_, lean_object* v_usedLetOnly_1575_, lean_object* v_skipConstInApp_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v_skipInstances_boxed_1586_; uint8_t v_usedLetOnly_boxed_1587_; uint8_t v_skipConstInApp_boxed_1588_; lean_object* v_res_1589_; 
v_skipInstances_boxed_1586_ = lean_unbox(v_skipInstances_1572_);
v_usedLetOnly_boxed_1587_ = lean_unbox(v_usedLetOnly_1575_);
v_skipConstInApp_boxed_1588_ = lean_unbox(v_skipConstInApp_1576_);
v_res_1589_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1586_, v_pre_1573_, v_post_1574_, v_usedLetOnly_boxed_1587_, v_skipConstInApp_boxed_1588_, v_x_1577_, v_x_1578_, v_x_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
return v_res_1589_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_unsigned_to_nat(16u);
v___x_1592_ = lean_mk_array(v___x_1591_, v___x_1590_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1597_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1597_, 0, lean_box(0));
lean_closure_set(v___x_1597_, 1, lean_box(0));
lean_closure_set(v___x_1597_, 2, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1598_, lean_object* v_pre_1599_, lean_object* v_post_1600_, uint8_t v_usedLetOnly_1601_, uint8_t v_skipConstInApp_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_a_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1608_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1609_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1608_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = 0;
v___x_1612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1599_, v_post_1600_, v_usedLetOnly_1601_, v_skipConstInApp_1602_, v___x_1611_, v_input_1598_, v_a_1610_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1614_, 0, lean_box(0));
lean_closure_set(v___x_1614_, 1, lean_box(0));
lean_closure_set(v___x_1614_, 2, v_a_1610_);
v___x_1615_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1614_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v___x_1615_, 0);
lean_dec(v_unused_1623_);
v___x_1617_ = v___x_1615_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v___x_1615_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_a_1613_);
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1613_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_dec(v_a_1610_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1624_, lean_object* v_pre_1625_, lean_object* v_post_1626_, lean_object* v_usedLetOnly_1627_, lean_object* v_skipConstInApp_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v_usedLetOnly_boxed_1634_; uint8_t v_skipConstInApp_boxed_1635_; lean_object* v_res_1636_; 
v_usedLetOnly_boxed_1634_ = lean_unbox(v_usedLetOnly_1627_);
v_skipConstInApp_boxed_1635_ = lean_unbox(v_skipConstInApp_1628_);
v_res_1636_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1624_, v_pre_1625_, v_post_1626_, v_usedLetOnly_boxed_1634_, v_skipConstInApp_boxed_1635_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1636_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__1(void){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Array_instInhabited(lean_box(0));
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__3(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__2));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__5(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__4));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1645_, lean_object* v_argsPacker_1646_, lean_object* v_funNames_1647_, lean_object* v_newF_1648_, lean_object* v_e_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; 
lean_inc(v_a_1653_);
lean_inc_ref(v_a_1652_);
lean_inc(v_a_1651_);
lean_inc_ref(v_a_1650_);
lean_inc_ref(v_newF_1648_);
v___x_1655_ = lean_infer_type(v_newF_1648_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; uint8_t v___x_1669_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___f_1657_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1658_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_1669_ = l_Lean_Expr_isForall(v_a_1656_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v_e_1649_);
lean_dec_ref(v_funNames_1647_);
lean_dec_ref(v_argsPacker_1646_);
lean_dec_ref(v_fixedParamPerms_1645_);
v___x_1670_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__3, &l_Lean_Elab_WF_packCalls___closed__3_once, _init_l_Lean_Elab_WF_packCalls___closed__3);
v___x_1671_ = l_Lean_MessageData_ofExpr(v_newF_1648_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__5, &l_Lean_Elab_WF_packCalls___closed__5_once, _init_l_Lean_Elab_WF_packCalls___closed__5);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = l_Lean_MessageData_ofExpr(v_a_1656_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1676_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
v___y_1660_ = v_a_1650_;
v___y_1661_ = v_a_1651_;
v___y_1662_ = v_a_1652_;
v___y_1663_ = v_a_1653_;
goto v___jp_1659_;
}
v___jp_1659_:
{
lean_object* v___x_1664_; lean_object* v___f_1665_; uint8_t v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1664_ = l_Lean_Expr_bindingDomain_x21(v_a_1656_);
lean_dec(v_a_1656_);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 12, 6);
lean_closure_set(v___f_1665_, 0, v_funNames_1647_);
lean_closure_set(v___f_1665_, 1, v_fixedParamPerms_1645_);
lean_closure_set(v___f_1665_, 2, v___x_1658_);
lean_closure_set(v___f_1665_, 3, v_argsPacker_1646_);
lean_closure_set(v___f_1665_, 4, v___x_1664_);
lean_closure_set(v___f_1665_, 5, v_newF_1648_);
v___x_1666_ = 0;
v___x_1667_ = 1;
v___x_1668_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1649_, v___f_1657_, v___f_1665_, v___x_1666_, v___x_1667_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1668_;
}
}
else
{
lean_dec_ref(v_e_1649_);
lean_dec_ref(v_newF_1648_);
lean_dec_ref(v_funNames_1647_);
lean_dec_ref(v_argsPacker_1646_);
lean_dec_ref(v_fixedParamPerms_1645_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1686_, lean_object* v_argsPacker_1687_, lean_object* v_funNames_1688_, lean_object* v_newF_1689_, lean_object* v_e_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1686_, v_argsPacker_1687_, v_funNames_1688_, v_newF_1689_, v_e_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1697_, lean_object* v___x_1698_, lean_object* v_pre_1699_, lean_object* v_post_1700_, uint8_t v_usedLetOnly_1701_, uint8_t v_skipConstInApp_1702_, uint8_t v_skipInstances_1703_, lean_object* v___x_1704_, lean_object* v_inst_1705_, lean_object* v_R_1706_, lean_object* v_a_1707_, lean_object* v_b_1708_, lean_object* v_c_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1697_, v___x_1698_, v_pre_1699_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_a_1707_, v_b_1708_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1717_ = _args[0];
lean_object* v___x_1718_ = _args[1];
lean_object* v_pre_1719_ = _args[2];
lean_object* v_post_1720_ = _args[3];
lean_object* v_usedLetOnly_1721_ = _args[4];
lean_object* v_skipConstInApp_1722_ = _args[5];
lean_object* v_skipInstances_1723_ = _args[6];
lean_object* v___x_1724_ = _args[7];
lean_object* v_inst_1725_ = _args[8];
lean_object* v_R_1726_ = _args[9];
lean_object* v_a_1727_ = _args[10];
lean_object* v_b_1728_ = _args[11];
lean_object* v_c_1729_ = _args[12];
lean_object* v___y_1730_ = _args[13];
lean_object* v___y_1731_ = _args[14];
lean_object* v___y_1732_ = _args[15];
lean_object* v___y_1733_ = _args[16];
lean_object* v___y_1734_ = _args[17];
lean_object* v___y_1735_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1736_; uint8_t v_skipConstInApp_boxed_1737_; uint8_t v_skipInstances_boxed_1738_; lean_object* v_res_1739_; 
v_usedLetOnly_boxed_1736_ = lean_unbox(v_usedLetOnly_1721_);
v_skipConstInApp_boxed_1737_ = lean_unbox(v_skipConstInApp_1722_);
v_skipInstances_boxed_1738_ = lean_unbox(v_skipInstances_1723_);
v_res_1739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1717_, v___x_1718_, v_pre_1719_, v_post_1720_, v_usedLetOnly_boxed_1736_, v_skipConstInApp_boxed_1737_, v_skipInstances_boxed_1738_, v___x_1724_, v_inst_1725_, v_R_1726_, v_a_1727_, v_b_1728_, v_c_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec(v___x_1724_);
lean_dec_ref(v___x_1718_);
lean_dec(v_upperBound_1717_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1740_, lean_object* v_m_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1741_, v_a_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1744_, lean_object* v_m_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1744_, v_m_1745_, v_a_1746_);
lean_dec_ref(v_a_1746_);
lean_dec_ref(v_m_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1748_, lean_object* v_name_1749_, uint8_t v_bi_1750_, lean_object* v_type_1751_, lean_object* v_k_1752_, uint8_t v_kind_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1749_, v_bi_1750_, v_type_1751_, v_k_1752_, v_kind_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_name_1762_, lean_object* v_bi_1763_, lean_object* v_type_1764_, lean_object* v_k_1765_, lean_object* v_kind_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_bi_boxed_1773_; uint8_t v_kind_boxed_1774_; lean_object* v_res_1775_; 
v_bi_boxed_1773_ = lean_unbox(v_bi_1763_);
v_kind_boxed_1774_ = lean_unbox(v_kind_1766_);
v_res_1775_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1761_, v_name_1762_, v_bi_boxed_1773_, v_type_1764_, v_k_1765_, v_kind_boxed_1774_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1776_, lean_object* v_name_1777_, lean_object* v_type_1778_, lean_object* v_val_1779_, lean_object* v_k_1780_, uint8_t v_nondep_1781_, uint8_t v_kind_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1777_, v_type_1778_, v_val_1779_, v_k_1780_, v_nondep_1781_, v_kind_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_name_1791_, lean_object* v_type_1792_, lean_object* v_val_1793_, lean_object* v_k_1794_, lean_object* v_nondep_1795_, lean_object* v_kind_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v_nondep_boxed_1803_; uint8_t v_kind_boxed_1804_; lean_object* v_res_1805_; 
v_nondep_boxed_1803_ = lean_unbox(v_nondep_1795_);
v_kind_boxed_1804_ = lean_unbox(v_kind_1796_);
v_res_1805_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1790_, v_name_1791_, v_type_1792_, v_val_1793_, v_k_1794_, v_nondep_boxed_1803_, v_kind_boxed_1804_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1806_, lean_object* v_ref_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1807_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1814_, lean_object* v_ref_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1814_, v_ref_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1831_, v_x_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1840_, lean_object* v_m_1841_, lean_object* v_a_1842_, lean_object* v_b_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1841_, v_a_1842_, v_b_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1845_, lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1849_, lean_object* v_a_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1849_, v_a_1850_, v_x_1851_);
lean_dec(v_x_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1853_, lean_object* v_a_1854_, lean_object* v_x_1855_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1857_, lean_object* v_a_1858_, lean_object* v_x_1859_){
_start:
{
uint8_t v_res_1860_; lean_object* v_r_1861_; 
v_res_1860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1857_, v_a_1858_, v_x_1859_);
lean_dec(v_x_1859_);
lean_dec_ref(v_a_1858_);
v_r_1861_ = lean_box(v_res_1860_);
return v_r_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1862_, lean_object* v_data_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1865_, lean_object* v_a_1866_, lean_object* v_b_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1866_, v_b_1867_, v_x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1870_, lean_object* v_i_1871_, lean_object* v_source_1872_, lean_object* v_target_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1871_, v_source_1872_, v_target_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1876_, v_x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1885_, lean_object* v_argsPacker_1886_, lean_object* v_preDefs_1887_){
_start:
{
lean_object* v___x_1888_; uint8_t v___y_1890_; uint8_t v___x_1907_; 
v___x_1888_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1907_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1885_);
if (v___x_1907_ == 0)
{
v___y_1890_ = v___x_1907_;
goto v___jp_1889_;
}
else
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1886_);
v___y_1890_ = v___x_1908_;
goto v___jp_1889_;
}
v___jp_1889_:
{
if (v___y_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1886_);
v___x_1893_ = lean_nat_dec_lt(v___x_1891_, v___x_1892_);
lean_dec(v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_declName_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_array_get_borrowed(v___x_1888_, v_preDefs_1887_, v___x_1894_);
v_declName_1896_ = lean_ctor_get(v___x_1895_, 3);
v___x_1897_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1896_);
v___x_1898_ = l_Lean_Name_append(v_declName_1896_, v___x_1897_);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_declName_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_array_get_borrowed(v___x_1888_, v_preDefs_1887_, v___x_1899_);
v_declName_1901_ = lean_ctor_get(v___x_1900_, 3);
v___x_1902_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1901_);
v___x_1903_ = l_Lean_Name_append(v_declName_1901_, v___x_1902_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_declName_1906_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_array_get_borrowed(v___x_1888_, v_preDefs_1887_, v___x_1904_);
v_declName_1906_ = lean_ctor_get(v___x_1905_, 3);
lean_inc(v_declName_1906_);
return v_declName_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1909_, lean_object* v_argsPacker_1910_, lean_object* v_preDefs_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1909_, v_argsPacker_1910_, v_preDefs_1911_);
lean_dec_ref(v_preDefs_1911_);
lean_dec_ref(v_argsPacker_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1913_, lean_object* v_b_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
lean_inc(v___y_1918_);
lean_inc_ref(v___y_1917_);
lean_inc(v___y_1916_);
lean_inc_ref(v___y_1915_);
v___x_1920_ = lean_apply_6(v_k_1913_, v_b_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, lean_box(0));
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1921_, v_b_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1929_, lean_object* v_type_1930_, lean_object* v_k_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1937_, 0, v_k_1931_);
v___x_1938_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1929_, v_type_1930_, v___f_1937_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1938_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1938_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1955_, lean_object* v_type_1956_, lean_object* v_k_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1955_, v_type_1956_, v_k_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1964_, lean_object* v_perm_1965_, lean_object* v_type_1966_, lean_object* v_k_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1965_, v_type_1966_, v_k_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1974_, lean_object* v_perm_1975_, lean_object* v_type_1976_, lean_object* v_k_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1974_, v_perm_1975_, v_type_1976_, v_k_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1984_, lean_object* v_ys_1985_, size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_bs_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_lt(v_i_1987_, v_sz_1986_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec_ref(v_ys_1985_);
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v_bs_1988_);
return v___x_1995_;
}
else
{
lean_object* v_v_1996_; lean_object* v_value_1997_; lean_object* v___x_1998_; lean_object* v_bs_x27_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_v_1996_ = lean_array_uget_borrowed(v_bs_1988_, v_i_1987_);
v_value_1997_ = lean_ctor_get(v_v_1996_, 7);
lean_inc_ref(v_value_1997_);
v___x_1998_ = lean_unsigned_to_nat(0u);
v_bs_x27_1999_ = lean_array_uset(v_bs_1988_, v_i_1987_, v___x_1998_);
v___x_2000_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2001_ = lean_usize_to_nat(v_i_1987_);
v___x_2002_ = lean_array_get_borrowed(v___x_2000_, v___x_1984_, v___x_2001_);
lean_dec(v___x_2001_);
lean_inc_ref(v_ys_1985_);
lean_inc(v___x_2002_);
v___x_2003_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2002_, v_value_1997_, v_ys_1985_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_add(v_i_1987_, v___x_2005_);
v___x_2007_ = lean_array_uset(v_bs_x27_1999_, v_i_1987_, v_a_2004_);
v_i_1987_ = v___x_2006_;
v_bs_1988_ = v___x_2007_;
goto _start;
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_bs_x27_1999_);
lean_dec_ref(v_ys_1985_);
v_a_2009_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2003_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2003_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2017_, lean_object* v_ys_2018_, lean_object* v_sz_2019_, lean_object* v_i_2020_, lean_object* v_bs_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
size_t v_sz_boxed_2027_; size_t v_i_boxed_2028_; lean_object* v_res_2029_; 
v_sz_boxed_2027_ = lean_unbox_usize(v_sz_2019_);
lean_dec(v_sz_2019_);
v_i_boxed_2028_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v_res_2029_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2017_, v_ys_2018_, v_sz_boxed_2027_, v_i_boxed_2028_, v_bs_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v___x_2017_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2030_, lean_object* v_ys_2031_, size_t v_sz_2032_, size_t v_i_2033_, lean_object* v_bs_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v___x_2040_; 
v___x_2040_ = lean_usize_dec_lt(v_i_2033_, v_sz_2032_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec_ref(v_ys_2031_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_bs_2034_);
return v___x_2041_;
}
else
{
lean_object* v_v_2042_; lean_object* v_type_2043_; lean_object* v___x_2044_; lean_object* v_bs_x27_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_v_2042_ = lean_array_uget_borrowed(v_bs_2034_, v_i_2033_);
v_type_2043_ = lean_ctor_get(v_v_2042_, 6);
lean_inc_ref(v_type_2043_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v_bs_x27_2045_ = lean_array_uset(v_bs_2034_, v_i_2033_, v___x_2044_);
v___x_2046_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2047_ = lean_usize_to_nat(v_i_2033_);
v___x_2048_ = lean_array_get_borrowed(v___x_2046_, v___x_2030_, v___x_2047_);
lean_dec(v___x_2047_);
lean_inc_ref(v_ys_2031_);
lean_inc(v___x_2048_);
v___x_2049_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2048_, v_type_2043_, v_ys_2031_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; size_t v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = ((size_t)1ULL);
v___x_2052_ = lean_usize_add(v_i_2033_, v___x_2051_);
v___x_2053_ = lean_array_uset(v_bs_x27_2045_, v_i_2033_, v_a_2050_);
v_i_2033_ = v___x_2052_;
v_bs_2034_ = v___x_2053_;
goto _start;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_bs_x27_2045_);
lean_dec_ref(v_ys_2031_);
v_a_2055_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2049_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2049_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2063_, lean_object* v_ys_2064_, lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_bs_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
size_t v_sz_boxed_2073_; size_t v_i_boxed_2074_; lean_object* v_res_2075_; 
v_sz_boxed_2073_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2074_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2063_, v_ys_2064_, v_sz_boxed_2073_, v_i_boxed_2074_, v_bs_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec_ref(v___x_2063_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
if (lean_obj_tag(v_a_2076_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = l_List_reverse___redArg(v_a_2077_);
return v___x_2078_;
}
else
{
lean_object* v_head_2079_; lean_object* v_tail_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2089_; 
v_head_2079_ = lean_ctor_get(v_a_2076_, 0);
v_tail_2080_ = lean_ctor_get(v_a_2076_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_a_2076_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2082_ = v_a_2076_;
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_tail_2080_);
lean_inc(v_head_2079_);
lean_dec(v_a_2076_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = l_Lean_mkLevelParam(v_head_2079_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_a_2077_);
lean_ctor_set(v___x_2082_, 0, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_a_2077_);
v___x_2086_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v_a_2076_ = v_tail_2080_;
v_a_2077_ = v___x_2086_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2090_, size_t v_i_2091_, lean_object* v_bs_2092_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2091_, v_sz_2090_);
if (v___x_2093_ == 0)
{
return v_bs_2092_;
}
else
{
lean_object* v_v_2094_; lean_object* v_declName_2095_; lean_object* v___x_2096_; lean_object* v_bs_x27_2097_; size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v_v_2094_ = lean_array_uget_borrowed(v_bs_2092_, v_i_2091_);
v_declName_2095_ = lean_ctor_get(v_v_2094_, 3);
lean_inc(v_declName_2095_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v_bs_x27_2097_ = lean_array_uset(v_bs_2092_, v_i_2091_, v___x_2096_);
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_add(v_i_2091_, v___x_2098_);
v___x_2100_ = lean_array_uset(v_bs_x27_2097_, v_i_2091_, v_declName_2095_);
v_i_2091_ = v___x_2099_;
v_bs_2092_ = v___x_2100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2102_, lean_object* v_i_2103_, lean_object* v_bs_2104_){
_start:
{
size_t v_sz_boxed_2105_; size_t v_i_boxed_2106_; lean_object* v_res_2107_; 
v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2102_);
lean_dec(v_sz_2102_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2103_);
lean_dec(v_i_2103_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2105_, v_i_boxed_2106_, v_bs_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2108_, lean_object* v_perms_2109_, lean_object* v_argsPacker_2110_, uint8_t v___x_2111_, lean_object* v_ref_2112_, uint8_t v_kind_2113_, lean_object* v_levelParams_2114_, lean_object* v_modifiers_2115_, lean_object* v_newFn_2116_, lean_object* v_binders_2117_, lean_object* v_numSectionVars_2118_, lean_object* v_value_2119_, lean_object* v_termination_2120_, lean_object* v_fixedParamPerms_2121_, lean_object* v_ys_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
size_t v_sz_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v_sz_2128_ = lean_array_size(v_preDefs_2108_);
v___x_2129_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2108_);
lean_inc_ref(v_ys_2122_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2109_, v_ys_2122_, v_sz_2128_, v___x_2129_, v_preDefs_2108_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
lean_inc_ref(v_preDefs_2108_);
lean_inc_ref(v_ys_2122_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2109_, v_ys_2122_, v_sz_2128_, v___x_2129_, v_preDefs_2108_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2110_, v_a_2131_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v_a_2131_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = 1;
v___x_2137_ = 1;
v___x_2138_ = l_Lean_Meta_mkForallFVars(v_ys_2122_, v_a_2135_, v___x_2111_, v___x_2136_, v___x_2136_, v___x_2137_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_n(v_a_2139_, 2);
lean_dec_ref_known(v___x_2138_, 1);
lean_inc_ref(v_termination_2120_);
lean_inc(v_numSectionVars_2118_);
lean_inc(v_binders_2117_);
lean_inc(v_newFn_2116_);
lean_inc_ref(v_modifiers_2115_);
lean_inc(v_levelParams_2114_);
lean_inc(v_ref_2112_);
v___x_2140_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2140_, 0, v_ref_2112_);
lean_ctor_set(v___x_2140_, 1, v_levelParams_2114_);
lean_ctor_set(v___x_2140_, 2, v_modifiers_2115_);
lean_ctor_set(v___x_2140_, 3, v_newFn_2116_);
lean_ctor_set(v___x_2140_, 4, v_binders_2117_);
lean_ctor_set(v___x_2140_, 5, v_numSectionVars_2118_);
lean_ctor_set(v___x_2140_, 6, v_a_2139_);
lean_ctor_set(v___x_2140_, 7, v_value_2119_);
lean_ctor_set(v___x_2140_, 8, v_termination_2120_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*9, v_kind_2113_);
v___x_2141_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2140_, v___y_2125_, v___y_2126_);
lean_dec_ref_known(v___x_2140_, 9);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; 
lean_dec_ref_known(v___x_2141_, 1);
v___x_2142_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2110_, v_a_2133_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v_a_2133_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = lean_box(0);
lean_inc(v_levelParams_2114_);
v___x_2145_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2114_, v___x_2144_);
lean_inc(v_newFn_2116_);
v___x_2146_ = l_Lean_mkConst(v_newFn_2116_, v___x_2145_);
v___x_2147_ = l_Lean_mkAppN(v___x_2146_, v_ys_2122_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2128_, v___x_2129_, v_preDefs_2108_);
v___x_2149_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2121_, v_argsPacker_2110_, v___x_2148_, v___x_2147_, v_a_2143_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Meta_mkLambdaFVars(v_ys_2122_, v_a_2150_, v___x_2111_, v___x_2136_, v___x_2111_, v___x_2136_, v___x_2137_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec_ref(v_ys_2122_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2160_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2156_, 0, v_ref_2112_);
lean_ctor_set(v___x_2156_, 1, v_levelParams_2114_);
lean_ctor_set(v___x_2156_, 2, v_modifiers_2115_);
lean_ctor_set(v___x_2156_, 3, v_newFn_2116_);
lean_ctor_set(v___x_2156_, 4, v_binders_2117_);
lean_ctor_set(v___x_2156_, 5, v_numSectionVars_2118_);
lean_ctor_set(v___x_2156_, 6, v_a_2139_);
lean_ctor_set(v___x_2156_, 7, v_a_2152_);
lean_ctor_set(v___x_2156_, 8, v_termination_2120_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*9, v_kind_2113_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2139_);
lean_dec_ref(v_termination_2120_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
v_a_2161_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2151_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2151_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_a_2139_);
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_termination_2120_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
v_a_2169_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2149_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2149_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_a_2139_);
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_termination_2120_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
lean_dec_ref(v_argsPacker_2110_);
lean_dec_ref(v_preDefs_2108_);
v_a_2177_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2142_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2142_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2139_);
lean_dec(v_a_2133_);
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_termination_2120_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
lean_dec_ref(v_argsPacker_2110_);
lean_dec_ref(v_preDefs_2108_);
v_a_2185_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2141_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2141_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_a_2133_);
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_termination_2120_);
lean_dec_ref(v_value_2119_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
lean_dec_ref(v_argsPacker_2110_);
lean_dec_ref(v_preDefs_2108_);
v_a_2193_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2138_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2138_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_a_2133_);
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_termination_2120_);
lean_dec_ref(v_value_2119_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
lean_dec_ref(v_argsPacker_2110_);
lean_dec_ref(v_preDefs_2108_);
v_a_2201_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2134_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2134_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_a_2131_);
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_termination_2120_);
lean_dec_ref(v_value_2119_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
lean_dec_ref(v_argsPacker_2110_);
lean_dec_ref(v_preDefs_2108_);
v_a_2209_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2132_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2132_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_ys_2122_);
lean_dec_ref(v_fixedParamPerms_2121_);
lean_dec_ref(v_termination_2120_);
lean_dec_ref(v_value_2119_);
lean_dec(v_numSectionVars_2118_);
lean_dec(v_binders_2117_);
lean_dec(v_newFn_2116_);
lean_dec_ref(v_modifiers_2115_);
lean_dec(v_levelParams_2114_);
lean_dec(v_ref_2112_);
lean_dec_ref(v_argsPacker_2110_);
lean_dec_ref(v_preDefs_2108_);
v_a_2217_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2130_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2130_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2225_ = _args[0];
lean_object* v_perms_2226_ = _args[1];
lean_object* v_argsPacker_2227_ = _args[2];
lean_object* v___x_2228_ = _args[3];
lean_object* v_ref_2229_ = _args[4];
lean_object* v_kind_2230_ = _args[5];
lean_object* v_levelParams_2231_ = _args[6];
lean_object* v_modifiers_2232_ = _args[7];
lean_object* v_newFn_2233_ = _args[8];
lean_object* v_binders_2234_ = _args[9];
lean_object* v_numSectionVars_2235_ = _args[10];
lean_object* v_value_2236_ = _args[11];
lean_object* v_termination_2237_ = _args[12];
lean_object* v_fixedParamPerms_2238_ = _args[13];
lean_object* v_ys_2239_ = _args[14];
lean_object* v___y_2240_ = _args[15];
lean_object* v___y_2241_ = _args[16];
lean_object* v___y_2242_ = _args[17];
lean_object* v___y_2243_ = _args[18];
lean_object* v___y_2244_ = _args[19];
_start:
{
uint8_t v___x_2504__boxed_2245_; uint8_t v_kind_boxed_2246_; lean_object* v_res_2247_; 
v___x_2504__boxed_2245_ = lean_unbox(v___x_2228_);
v_kind_boxed_2246_ = lean_unbox(v_kind_2230_);
v_res_2247_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2225_, v_perms_2226_, v_argsPacker_2227_, v___x_2504__boxed_2245_, v_ref_2229_, v_kind_boxed_2246_, v_levelParams_2231_, v_modifiers_2232_, v_newFn_2233_, v_binders_2234_, v_numSectionVars_2235_, v_value_2236_, v_termination_2237_, v_fixedParamPerms_2238_, v_ys_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_perms_2226_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2248_, lean_object* v_argsPacker_2249_, lean_object* v_preDefs_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_ref_2259_; uint8_t v_kind_2260_; lean_object* v_levelParams_2261_; lean_object* v_modifiers_2262_; lean_object* v_declName_2263_; lean_object* v_binders_2264_; lean_object* v_numSectionVars_2265_; lean_object* v_type_2266_; lean_object* v_value_2267_; lean_object* v_termination_2268_; lean_object* v_newFn_2269_; uint8_t v___x_2270_; 
v___x_2256_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = lean_array_get_borrowed(v___x_2256_, v_preDefs_2250_, v___x_2257_);
v_ref_2259_ = lean_ctor_get(v___x_2258_, 0);
v_kind_2260_ = lean_ctor_get_uint8(v___x_2258_, sizeof(void*)*9);
v_levelParams_2261_ = lean_ctor_get(v___x_2258_, 1);
v_modifiers_2262_ = lean_ctor_get(v___x_2258_, 2);
v_declName_2263_ = lean_ctor_get(v___x_2258_, 3);
v_binders_2264_ = lean_ctor_get(v___x_2258_, 4);
v_numSectionVars_2265_ = lean_ctor_get(v___x_2258_, 5);
v_type_2266_ = lean_ctor_get(v___x_2258_, 6);
v_value_2267_ = lean_ctor_get(v___x_2258_, 7);
v_termination_2268_ = lean_ctor_get(v___x_2258_, 8);
lean_inc_ref(v_fixedParamPerms_2248_);
v_newFn_2269_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2248_, v_argsPacker_2249_, v_preDefs_2250_);
v___x_2270_ = lean_name_eq(v_newFn_2269_, v_declName_2263_);
if (v___x_2270_ == 0)
{
lean_object* v_perms_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_inc_ref(v_termination_2268_);
lean_inc_ref(v_value_2267_);
lean_inc_ref(v_type_2266_);
lean_inc(v_numSectionVars_2265_);
lean_inc(v_binders_2264_);
lean_inc_ref(v_modifiers_2262_);
lean_inc(v_levelParams_2261_);
lean_inc(v_ref_2259_);
v_perms_2271_ = lean_ctor_get(v_fixedParamPerms_2248_, 1);
lean_inc_ref_n(v_perms_2271_, 2);
v___x_2272_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2273_ = lean_box(v___x_2270_);
v___x_2274_ = lean_box(v_kind_2260_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2275_, 0, v_preDefs_2250_);
lean_closure_set(v___f_2275_, 1, v_perms_2271_);
lean_closure_set(v___f_2275_, 2, v_argsPacker_2249_);
lean_closure_set(v___f_2275_, 3, v___x_2273_);
lean_closure_set(v___f_2275_, 4, v_ref_2259_);
lean_closure_set(v___f_2275_, 5, v___x_2274_);
lean_closure_set(v___f_2275_, 6, v_levelParams_2261_);
lean_closure_set(v___f_2275_, 7, v_modifiers_2262_);
lean_closure_set(v___f_2275_, 8, v_newFn_2269_);
lean_closure_set(v___f_2275_, 9, v_binders_2264_);
lean_closure_set(v___f_2275_, 10, v_numSectionVars_2265_);
lean_closure_set(v___f_2275_, 11, v_value_2267_);
lean_closure_set(v___f_2275_, 12, v_termination_2268_);
lean_closure_set(v___f_2275_, 13, v_fixedParamPerms_2248_);
v___x_2276_ = lean_array_get(v___x_2272_, v_perms_2271_, v___x_2257_);
lean_dec_ref(v_perms_2271_);
v___x_2277_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2276_, v_type_2266_, v___f_2275_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; 
lean_inc(v___x_2258_);
lean_dec(v_newFn_2269_);
lean_dec_ref(v_preDefs_2250_);
lean_dec_ref(v_argsPacker_2249_);
lean_dec_ref(v_fixedParamPerms_2248_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2258_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2279_, lean_object* v_argsPacker_2280_, lean_object* v_preDefs_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2279_, v_argsPacker_2280_, v_preDefs_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2288_, lean_object* v_ys_2289_, lean_object* v_as_2290_, size_t v_sz_2291_, size_t v_i_2292_, lean_object* v_bs_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2288_, v_ys_2289_, v_sz_2291_, v_i_2292_, v_bs_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2300_, lean_object* v_ys_2301_, lean_object* v_as_2302_, lean_object* v_sz_2303_, lean_object* v_i_2304_, lean_object* v_bs_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2303_);
lean_dec(v_sz_2303_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2304_);
lean_dec(v_i_2304_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2300_, v_ys_2301_, v_as_2302_, v_sz_boxed_2311_, v_i_boxed_2312_, v_bs_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v_as_2302_);
lean_dec_ref(v___x_2300_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2314_, lean_object* v_ys_2315_, lean_object* v_as_2316_, size_t v_sz_2317_, size_t v_i_2318_, lean_object* v_bs_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2314_, v_ys_2315_, v_sz_2317_, v_i_2318_, v_bs_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2326_, lean_object* v_ys_2327_, lean_object* v_as_2328_, lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_bs_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
size_t v_sz_boxed_2337_; size_t v_i_boxed_2338_; lean_object* v_res_2339_; 
v_sz_boxed_2337_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2338_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2326_, v_ys_2327_, v_as_2328_, v_sz_boxed_2337_, v_i_boxed_2338_, v_bs_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_as_2328_);
lean_dec_ref(v___x_2326_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2340_, lean_object* v_k_2341_, uint8_t v_cleanupAnnotations_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___f_2348_; uint8_t v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2348_, 0, v_k_2341_);
v___x_2349_ = 1;
v___x_2350_ = 0;
v___x_2351_ = lean_box(0);
v___x_2352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2340_, v___x_2349_, v___x_2350_, v___x_2349_, v___x_2350_, v___x_2351_, v___f_2348_, v_cleanupAnnotations_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2352_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2352_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2369_, lean_object* v_k_2370_, lean_object* v_cleanupAnnotations_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2377_; lean_object* v_res_2378_; 
v_cleanupAnnotations_boxed_2377_ = lean_unbox(v_cleanupAnnotations_2371_);
v_res_2378_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2369_, v_k_2370_, v_cleanupAnnotations_boxed_2377_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2379_, lean_object* v_e_2380_, lean_object* v_k_2381_, uint8_t v_cleanupAnnotations_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2380_, v_k_2381_, v_cleanupAnnotations_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_e_2390_, lean_object* v_k_2391_, lean_object* v_cleanupAnnotations_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2398_; lean_object* v_res_2399_; 
v_cleanupAnnotations_boxed_2398_ = lean_unbox(v_cleanupAnnotations_2392_);
v_res_2399_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2389_, v_e_2390_, v_k_2391_, v_cleanupAnnotations_boxed_2398_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___f_2406_; lean_object* v___x_1649__overap_2407_; lean_object* v___x_2408_; 
v___f_2406_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1649__overap_2407_ = lean_panic_fn_borrowed(v___f_2406_, v_msg_2400_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
v___x_2408_ = lean_apply_5(v___x_1649__overap_2407_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, lean_box(0));
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_array_get_size(v_xs_2416_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2425_, v_x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v_x_2426_);
lean_dec_ref(v_xs_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2433_, size_t v_sz_2434_, size_t v_i_2435_, lean_object* v_b_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_a_2442_; uint8_t v___x_2446_; 
v___x_2446_ = lean_usize_dec_lt(v_i_2435_, v_sz_2434_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v_b_2436_);
return v___x_2447_;
}
else
{
lean_object* v_snd_2448_; lean_object* v_fst_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2493_; 
v_snd_2448_ = lean_ctor_get(v_b_2436_, 1);
v_fst_2449_ = lean_ctor_get(v_b_2436_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_b_2436_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2451_ = v_b_2436_;
v_isShared_2452_ = v_isSharedCheck_2493_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_snd_2448_);
lean_inc(v_fst_2449_);
lean_dec(v_b_2436_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2493_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_array_2453_; lean_object* v_start_2454_; lean_object* v_stop_2455_; uint8_t v___x_2456_; 
v_array_2453_ = lean_ctor_get(v_snd_2448_, 0);
v_start_2454_ = lean_ctor_get(v_snd_2448_, 1);
v_stop_2455_ = lean_ctor_get(v_snd_2448_, 2);
v___x_2456_ = lean_nat_dec_lt(v_start_2454_, v_stop_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2458_; 
if (v_isShared_2452_ == 0)
{
v___x_2458_ = v___x_2451_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_fst_2449_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_snd_2448_);
v___x_2458_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
}
else
{
lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2489_; 
lean_inc(v_stop_2455_);
lean_inc(v_start_2454_);
lean_inc_ref(v_array_2453_);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_snd_2448_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; lean_object* v_unused_2491_; lean_object* v_unused_2492_; 
v_unused_2490_ = lean_ctor_get(v_snd_2448_, 2);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_snd_2448_, 1);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_snd_2448_, 0);
lean_dec(v_unused_2492_);
v___x_2462_ = v_snd_2448_;
v_isShared_2463_ = v_isSharedCheck_2489_;
goto v_resetjp_2461_;
}
else
{
lean_dec(v_snd_2448_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2489_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2464_ = lean_array_fget(v_array_2453_, v_start_2454_);
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_nat_add(v_start_2454_, v___x_2465_);
lean_dec(v_start_2454_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2466_);
v___x_2468_ = v___x_2462_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_array_2453_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_stop_2455_);
v___x_2468_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_a_2469_ = lean_array_uget_borrowed(v_as_2433_, v_i_2435_);
v___x_2470_ = l_Lean_Expr_fvarId_x21(v_a_2469_);
v___x_2471_ = l_Lean_FVarId_getUserName___redArg(v___x_2470_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2473_ = lean_array_push(v_fst_2449_, v_a_2472_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2468_);
lean_ctor_set(v___x_2451_, 0, v___x_2473_);
v___x_2475_ = v___x_2451_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2468_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
v_a_2442_ = v___x_2475_;
goto v___jp_2441_;
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v___x_2468_);
lean_del_object(v___x_2451_);
lean_dec(v_fst_2449_);
v_a_2477_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2471_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2471_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2464_, 1);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2468_);
v___x_2486_ = v___x_2451_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_fst_2449_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2468_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
v_a_2442_ = v___x_2486_;
goto v___jp_2441_;
}
}
}
}
}
}
}
v___jp_2441_:
{
size_t v___x_2443_; size_t v___x_2444_; 
v___x_2443_ = ((size_t)1ULL);
v___x_2444_ = lean_usize_add(v_i_2435_, v___x_2443_);
v_i_2435_ = v___x_2444_;
v_b_2436_ = v_a_2442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2494_, lean_object* v_sz_2495_, lean_object* v_i_2496_, lean_object* v_b_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2495_);
lean_dec(v_sz_2495_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2496_);
lean_dec(v_i_2496_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2494_, v_sz_boxed_2502_, v_i_boxed_2503_, v_b_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v_as_2494_);
return v_res_2504_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2507_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2508_ = lean_unsigned_to_nat(4u);
v___x_2509_ = lean_unsigned_to_nat(119u);
v___x_2510_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2511_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2512_ = l_mkPanicMessageWithDecl(v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_, v___x_2507_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2514_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2515_ = lean_unsigned_to_nat(4u);
v___x_2516_ = lean_unsigned_to_nat(120u);
v___x_2517_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2518_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2519_ = l_mkPanicMessageWithDecl(v___x_2518_, v___x_2517_, v___x_2516_, v___x_2515_, v___x_2514_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2522_, lean_object* v_fixedParamPerms_2523_, lean_object* v___x_2524_, lean_object* v_preDefIdx_2525_, lean_object* v_xs_2526_, lean_object* v_x_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_array_get_size(v_xs_2526_);
v___x_2534_ = lean_nat_dec_eq(v___x_2533_, v_a_2522_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2536_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2535_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v___x_2536_;
}
else
{
lean_object* v_perms_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_perms_2537_ = lean_ctor_get(v_fixedParamPerms_2523_, 1);
v___x_2538_ = lean_array_get_borrowed(v___x_2524_, v_perms_2537_, v_preDefIdx_2525_);
v___x_2539_ = lean_array_get_size(v___x_2538_);
v___x_2540_ = lean_nat_dec_eq(v___x_2539_, v_a_2522_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2542_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2541_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; size_t v_sz_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2538_);
v___x_2545_ = l_Array_toSubarray___redArg(v___x_2538_, v___x_2543_, v___x_2539_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v_sz_2547_ = lean_array_size(v_xs_2526_);
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2526_, v_sz_2547_, v___x_2548_, v___x_2546_, v___y_2528_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_fst_2554_; lean_object* v___x_2556_; 
v_fst_2554_ = lean_ctor_get(v_a_2550_, 0);
lean_inc(v_fst_2554_);
lean_dec(v_a_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v_fst_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_fst_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2549_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2549_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2567_, lean_object* v_fixedParamPerms_2568_, lean_object* v___x_2569_, lean_object* v_preDefIdx_2570_, lean_object* v_xs_2571_, lean_object* v_x_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2567_, v_fixedParamPerms_2568_, v___x_2569_, v_preDefIdx_2570_, v_xs_2571_, v_x_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v_x_2572_);
lean_dec_ref(v_xs_2571_);
lean_dec(v_preDefIdx_2570_);
lean_dec_ref(v___x_2569_);
lean_dec_ref(v_fixedParamPerms_2568_);
lean_dec(v_a_2567_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2580_, lean_object* v_preDefIdx_2581_, lean_object* v_preDef_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_type_2588_; lean_object* v_value_2589_; lean_object* v___f_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
v_type_2588_ = lean_ctor_get(v_preDef_2582_, 6);
lean_inc_ref(v_type_2588_);
v_value_2589_ = lean_ctor_get(v_preDef_2582_, 7);
lean_inc_ref(v_value_2589_);
lean_dec_ref(v_preDef_2582_);
v___f_2590_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2591_ = 0;
v___x_2592_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2589_, v___f_2590_, v___x_2591_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc_n(v_a_2593_, 2);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___f_2595_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2595_, 0, v_a_2593_);
lean_closure_set(v___f_2595_, 1, v_fixedParamPerms_2580_);
lean_closure_set(v___f_2595_, 2, v___x_2594_);
lean_closure_set(v___f_2595_, 3, v_preDefIdx_2581_);
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v_a_2593_);
v___x_2597_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2588_, v___x_2596_, v___f_2595_, v___x_2591_, v___x_2591_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
return v___x_2597_;
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref(v_type_2588_);
lean_dec(v_preDefIdx_2581_);
lean_dec_ref(v_fixedParamPerms_2580_);
v_a_2598_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2592_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2592_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2606_, lean_object* v_preDefIdx_2607_, lean_object* v_preDef_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2606_, v_preDefIdx_2607_, v_preDef_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2615_, size_t v_sz_2616_, size_t v_i_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2615_, v_sz_2616_, v_i_2617_, v_b_2618_, v___y_2619_, v___y_2621_, v___y_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2625_, lean_object* v_sz_2626_, lean_object* v_i_2627_, lean_object* v_b_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
size_t v_sz_boxed_2634_; size_t v_i_boxed_2635_; lean_object* v_res_2636_; 
v_sz_boxed_2634_ = lean_unbox_usize(v_sz_2626_);
lean_dec(v_sz_2626_);
v_i_boxed_2635_ = lean_unbox_usize(v_i_2627_);
lean_dec(v_i_2627_);
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2625_, v_sz_boxed_2634_, v_i_boxed_2635_, v_b_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v_as_2625_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___f_2643_; lean_object* v___x_1578__overap_2644_; lean_object* v___x_2645_; 
v___f_2643_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1578__overap_2644_ = lean_panic_fn_borrowed(v___f_2643_, v_msg_2637_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
v___x_2645_ = lean_apply_5(v___x_1578__overap_2644_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, lean_box(0));
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
return v_res_2652_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2653_; double v___x_2654_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_float_of_nat(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2658_, lean_object* v_msg_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_ref_2665_; lean_object* v___x_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2711_; 
v_ref_2665_ = lean_ctor_get(v___y_2662_, 2);
v___x_2666_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2711_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2711_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v_traceState_2672_; lean_object* v_env_2673_; lean_object* v_nextMacroScope_2674_; lean_object* v_ngen_2675_; lean_object* v_auxDeclNGen_2676_; lean_object* v_cache_2677_; lean_object* v_messages_2678_; lean_object* v_infoState_2679_; lean_object* v_snapshotTasks_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2710_; 
v___x_2671_ = lean_st_ref_take(v___y_2663_);
v_traceState_2672_ = lean_ctor_get(v___x_2671_, 4);
v_env_2673_ = lean_ctor_get(v___x_2671_, 0);
v_nextMacroScope_2674_ = lean_ctor_get(v___x_2671_, 1);
v_ngen_2675_ = lean_ctor_get(v___x_2671_, 2);
v_auxDeclNGen_2676_ = lean_ctor_get(v___x_2671_, 3);
v_cache_2677_ = lean_ctor_get(v___x_2671_, 5);
v_messages_2678_ = lean_ctor_get(v___x_2671_, 6);
v_infoState_2679_ = lean_ctor_get(v___x_2671_, 7);
v_snapshotTasks_2680_ = lean_ctor_get(v___x_2671_, 8);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2682_ = v___x_2671_;
v_isShared_2683_ = v_isSharedCheck_2710_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_snapshotTasks_2680_);
lean_inc(v_infoState_2679_);
lean_inc(v_messages_2678_);
lean_inc(v_cache_2677_);
lean_inc(v_traceState_2672_);
lean_inc(v_auxDeclNGen_2676_);
lean_inc(v_ngen_2675_);
lean_inc(v_nextMacroScope_2674_);
lean_inc(v_env_2673_);
lean_dec(v___x_2671_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2710_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
uint64_t v_tid_2684_; lean_object* v_traces_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2709_; 
v_tid_2684_ = lean_ctor_get_uint64(v_traceState_2672_, sizeof(void*)*1);
v_traces_2685_ = lean_ctor_get(v_traceState_2672_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_traceState_2672_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2687_ = v_traceState_2672_;
v_isShared_2688_ = v_isSharedCheck_2709_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_traces_2685_);
lean_dec(v_traceState_2672_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2709_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; double v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2691_ = 0;
v___x_2692_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2693_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2693_, 0, v_cls_2658_);
lean_ctor_set(v___x_2693_, 1, v___x_2689_);
lean_ctor_set(v___x_2693_, 2, v___x_2692_);
lean_ctor_set_float(v___x_2693_, sizeof(void*)*3, v___x_2690_);
lean_ctor_set_float(v___x_2693_, sizeof(void*)*3 + 8, v___x_2690_);
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*3 + 16, v___x_2691_);
v___x_2694_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2695_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v_a_2667_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
lean_inc(v_ref_2665_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_ref_2665_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_PersistentArray_push___redArg(v_traces_2685_, v___x_2696_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2697_);
v___x_2699_ = v___x_2687_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2697_);
lean_ctor_set_uint64(v_reuseFailAlloc_2708_, sizeof(void*)*1, v_tid_2684_);
v___x_2699_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 4, v___x_2699_);
v___x_2701_ = v___x_2682_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_env_2673_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_nextMacroScope_2674_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_ngen_2675_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_auxDeclNGen_2676_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_cache_2677_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_messages_2678_);
lean_ctor_set(v_reuseFailAlloc_2707_, 7, v_infoState_2679_);
lean_ctor_set(v_reuseFailAlloc_2707_, 8, v_snapshotTasks_2680_);
v___x_2701_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2702_ = lean_st_ref_put(v___y_2663_, v___x_2701_);
v___x_2703_ = lean_box(0);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2703_);
v___x_2705_ = v___x_2669_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2712_, lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2712_, v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2723_ = lean_unsigned_to_nat(8u);
v___x_2724_ = lean_unsigned_to_nat(135u);
v___x_2725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2726_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2727_ = l_mkPanicMessageWithDecl(v___x_2726_, v___x_2725_, v___x_2724_, v___x_2723_, v___x_2722_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2728_, lean_object* v_unaryPreDefNonRec_2729_, lean_object* v___x_2730_, lean_object* v_us_2731_, lean_object* v_argsPacker_2732_, lean_object* v___x_2733_, lean_object* v_params_2734_, lean_object* v_x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = lean_array_get_size(v_params_2734_);
v___x_2742_ = lean_nat_dec_eq(v___x_2728_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec(v___x_2733_);
lean_dec(v_us_2731_);
lean_dec_ref(v_unaryPreDefNonRec_2729_);
v___x_2743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2744_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2743_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2744_;
}
else
{
lean_object* v_declName_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_declName_2745_ = lean_ctor_get(v_unaryPreDefNonRec_2729_, 3);
lean_inc(v_declName_2745_);
lean_dec_ref(v_unaryPreDefNonRec_2729_);
v___x_2746_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2730_, v_params_2734_);
v___x_2747_ = l_Lean_mkConst(v_declName_2745_, v_us_2731_);
v___x_2748_ = l_Lean_mkAppN(v___x_2747_, v___x_2746_);
lean_dec_ref(v___x_2746_);
v___x_2749_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2732_, v___x_2748_, v___x_2733_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2730_, v_params_2734_);
v___x_2752_ = l_Lean_Expr_beta(v_a_2750_, v___x_2751_);
v___x_2753_ = 0;
v___x_2754_ = 1;
v___x_2755_ = l_Lean_Meta_mkLambdaFVars(v_params_2734_, v___x_2752_, v___x_2753_, v___x_2742_, v___x_2753_, v___x_2742_, v___x_2754_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2755_;
}
else
{
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2756_, lean_object* v_unaryPreDefNonRec_2757_, lean_object* v___x_2758_, lean_object* v_us_2759_, lean_object* v_argsPacker_2760_, lean_object* v___x_2761_, lean_object* v_params_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2756_, v_unaryPreDefNonRec_2757_, v___x_2758_, v_us_2759_, v_argsPacker_2760_, v___x_2761_, v_params_2762_, v_x_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec_ref(v_x_2763_);
lean_dec_ref(v_params_2762_);
lean_dec_ref(v_argsPacker_2760_);
lean_dec_ref(v___x_2758_);
lean_dec(v___x_2756_);
return v_res_2769_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2782_ = l_Lean_Name_append(v___x_2781_, v___x_2780_);
return v___x_2782_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2786_, lean_object* v_unaryPreDefNonRec_2787_, lean_object* v_us_2788_, lean_object* v_argsPacker_2789_, size_t v_sz_2790_, size_t v_i_2791_, lean_object* v_bs_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_usize_dec_lt(v_i_2791_, v_sz_2790_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
lean_dec_ref(v_argsPacker_2789_);
lean_dec(v_us_2788_);
lean_dec_ref(v_unaryPreDefNonRec_2787_);
v___x_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2799_, 0, v_bs_2792_);
return v___x_2799_;
}
else
{
lean_object* v_v_2800_; lean_object* v_perms_2801_; lean_object* v_ref_2802_; uint8_t v_kind_2803_; lean_object* v_levelParams_2804_; lean_object* v_modifiers_2805_; lean_object* v_declName_2806_; lean_object* v_binders_2807_; lean_object* v_numSectionVars_2808_; lean_object* v_type_2809_; lean_object* v_termination_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2862_; 
v_v_2800_ = lean_array_uget(v_bs_2792_, v_i_2791_);
v_perms_2801_ = lean_ctor_get(v_fixedParamPerms_2786_, 1);
v_ref_2802_ = lean_ctor_get(v_v_2800_, 0);
v_kind_2803_ = lean_ctor_get_uint8(v_v_2800_, sizeof(void*)*9);
v_levelParams_2804_ = lean_ctor_get(v_v_2800_, 1);
v_modifiers_2805_ = lean_ctor_get(v_v_2800_, 2);
v_declName_2806_ = lean_ctor_get(v_v_2800_, 3);
v_binders_2807_ = lean_ctor_get(v_v_2800_, 4);
v_numSectionVars_2808_ = lean_ctor_get(v_v_2800_, 5);
v_type_2809_ = lean_ctor_get(v_v_2800_, 6);
v_termination_2810_ = lean_ctor_get(v_v_2800_, 8);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_v_2800_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v_v_2800_, 7);
lean_dec(v_unused_2863_);
v___x_2812_ = v_v_2800_;
v_isShared_2813_ = v_isSharedCheck_2862_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_termination_2810_);
lean_inc(v_type_2809_);
lean_inc(v_numSectionVars_2808_);
lean_inc(v_binders_2807_);
lean_inc(v_declName_2806_);
lean_inc(v_modifiers_2805_);
lean_inc(v_levelParams_2804_);
lean_inc(v_ref_2802_);
lean_dec(v_v_2800_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2862_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v_bs_x27_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___f_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2814_ = lean_unsigned_to_nat(0u);
v_bs_x27_2815_ = lean_array_uset(v_bs_2792_, v_i_2791_, v___x_2814_);
v___x_2816_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__1, &l_Lean_Elab_WF_packCalls___closed__1_once, _init_l_Lean_Elab_WF_packCalls___closed__1);
v___x_2817_ = lean_usize_to_nat(v_i_2791_);
v___x_2818_ = lean_array_get_borrowed(v___x_2816_, v_perms_2801_, v___x_2817_);
v___x_2819_ = lean_array_get_size(v___x_2818_);
lean_inc_ref(v_argsPacker_2789_);
lean_inc(v_us_2788_);
lean_inc(v___x_2818_);
lean_inc_ref(v_unaryPreDefNonRec_2787_);
v___f_2820_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2820_, 0, v___x_2819_);
lean_closure_set(v___f_2820_, 1, v_unaryPreDefNonRec_2787_);
lean_closure_set(v___f_2820_, 2, v___x_2818_);
lean_closure_set(v___f_2820_, 3, v_us_2788_);
lean_closure_set(v___f_2820_, 4, v_argsPacker_2789_);
lean_closure_set(v___f_2820_, 5, v___x_2817_);
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
v___x_2822_ = 0;
lean_inc_ref(v_type_2809_);
v___x_2823_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2809_, v___x_2821_, v___f_2820_, v___x_2822_, v___x_2822_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v_toCold_2833_; lean_object* v_options_2834_; uint8_t v_hasTrace_2835_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v_toCold_2833_ = lean_ctor_get(v___y_2795_, 0);
v_options_2834_ = lean_ctor_get(v_toCold_2833_, 2);
v_hasTrace_2835_ = lean_ctor_get_uint8(v_options_2834_, sizeof(void*)*1);
if (v_hasTrace_2835_ == 0)
{
goto v___jp_2825_;
}
else
{
lean_object* v_inheritedTraceOptions_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v_inheritedTraceOptions_2836_ = lean_ctor_get(v_toCold_2833_, 11);
v___x_2837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2836_, v_options_2834_, v___x_2838_);
if (v___x_2839_ == 0)
{
goto v___jp_2825_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_inc(v_declName_2806_);
v___x_2840_ = l_Lean_MessageData_ofName(v_declName_2806_);
v___x_2841_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
lean_inc(v_a_2824_);
v___x_2843_ = l_Lean_MessageData_ofExpr(v_a_2824_);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2837_, v___x_2844_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_dec_ref_known(v___x_2845_, 1);
goto v___jp_2825_;
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_a_2824_);
lean_dec_ref(v_bs_x27_2815_);
lean_del_object(v___x_2812_);
lean_dec_ref(v_termination_2810_);
lean_dec_ref(v_type_2809_);
lean_dec(v_numSectionVars_2808_);
lean_dec(v_binders_2807_);
lean_dec(v_declName_2806_);
lean_dec_ref(v_modifiers_2805_);
lean_dec(v_levelParams_2804_);
lean_dec(v_ref_2802_);
lean_dec_ref(v_argsPacker_2789_);
lean_dec(v_us_2788_);
lean_dec_ref(v_unaryPreDefNonRec_2787_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
v___jp_2825_:
{
lean_object* v___x_2827_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 7, v_a_2824_);
v___x_2827_ = v___x_2812_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_ref_2802_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_levelParams_2804_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_modifiers_2805_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_declName_2806_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_binders_2807_);
lean_ctor_set(v_reuseFailAlloc_2832_, 5, v_numSectionVars_2808_);
lean_ctor_set(v_reuseFailAlloc_2832_, 6, v_type_2809_);
lean_ctor_set(v_reuseFailAlloc_2832_, 7, v_a_2824_);
lean_ctor_set(v_reuseFailAlloc_2832_, 8, v_termination_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*9, v_kind_2803_);
v___x_2827_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = ((size_t)1ULL);
v___x_2829_ = lean_usize_add(v_i_2791_, v___x_2828_);
v___x_2830_ = lean_array_uset(v_bs_x27_2815_, v_i_2791_, v___x_2827_);
v_i_2791_ = v___x_2829_;
v_bs_2792_ = v___x_2830_;
goto _start;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v_bs_x27_2815_);
lean_del_object(v___x_2812_);
lean_dec_ref(v_termination_2810_);
lean_dec_ref(v_type_2809_);
lean_dec(v_numSectionVars_2808_);
lean_dec(v_binders_2807_);
lean_dec(v_declName_2806_);
lean_dec_ref(v_modifiers_2805_);
lean_dec(v_levelParams_2804_);
lean_dec(v_ref_2802_);
lean_dec_ref(v_argsPacker_2789_);
lean_dec(v_us_2788_);
lean_dec_ref(v_unaryPreDefNonRec_2787_);
v_a_2854_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2823_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2823_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2864_, lean_object* v_unaryPreDefNonRec_2865_, lean_object* v_us_2866_, lean_object* v_argsPacker_2867_, lean_object* v_sz_2868_, lean_object* v_i_2869_, lean_object* v_bs_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2868_);
lean_dec(v_sz_2868_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2864_, v_unaryPreDefNonRec_2865_, v_us_2866_, v_argsPacker_2867_, v_sz_boxed_2876_, v_i_boxed_2877_, v_bs_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_fixedParamPerms_2864_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2879_, lean_object* v_preDefs_2880_, lean_object* v_fixedParamPerms_2881_, lean_object* v_us_2882_, lean_object* v_argsPacker_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2879_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2889_) == 0)
{
size_t v_sz_2890_; size_t v___x_2891_; lean_object* v___x_2892_; 
lean_dec_ref_known(v___x_2889_, 1);
v_sz_2890_ = lean_array_size(v_preDefs_2880_);
v___x_2891_ = ((size_t)0ULL);
v___x_2892_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2881_, v_unaryPreDefNonRec_2879_, v_us_2882_, v_argsPacker_2883_, v_sz_2890_, v___x_2891_, v_preDefs_2880_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v_argsPacker_2883_);
lean_dec(v_us_2882_);
lean_dec_ref(v_preDefs_2880_);
lean_dec_ref(v_unaryPreDefNonRec_2879_);
v_a_2893_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2889_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2889_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2901_, lean_object* v_preDefs_2902_, lean_object* v_fixedParamPerms_2903_, lean_object* v_us_2904_, lean_object* v_argsPacker_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2901_, v_preDefs_2902_, v_fixedParamPerms_2903_, v_us_2904_, v_argsPacker_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v_fixedParamPerms_2903_);
return v_res_2911_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2912_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
return v___x_2916_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2918_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
lean_ctor_set(v___x_2918_, 2, v___x_2917_);
lean_ctor_set(v___x_2918_, 3, v___x_2917_);
lean_ctor_set(v___x_2918_, 4, v___x_2917_);
lean_ctor_set(v___x_2918_, 5, v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v_nextMacroScope_2924_; lean_object* v_ngen_2925_; lean_object* v_auxDeclNGen_2926_; lean_object* v_traceState_2927_; lean_object* v_messages_2928_; lean_object* v_infoState_2929_; lean_object* v_snapshotTasks_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2956_; 
v___x_2923_ = lean_st_ref_take(v___y_2921_);
v_nextMacroScope_2924_ = lean_ctor_get(v___x_2923_, 1);
v_ngen_2925_ = lean_ctor_get(v___x_2923_, 2);
v_auxDeclNGen_2926_ = lean_ctor_get(v___x_2923_, 3);
v_traceState_2927_ = lean_ctor_get(v___x_2923_, 4);
v_messages_2928_ = lean_ctor_get(v___x_2923_, 6);
v_infoState_2929_ = lean_ctor_get(v___x_2923_, 7);
v_snapshotTasks_2930_ = lean_ctor_get(v___x_2923_, 8);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2956_ == 0)
{
lean_object* v_unused_2957_; lean_object* v_unused_2958_; 
v_unused_2957_ = lean_ctor_get(v___x_2923_, 5);
lean_dec(v_unused_2957_);
v_unused_2958_ = lean_ctor_get(v___x_2923_, 0);
lean_dec(v_unused_2958_);
v___x_2932_ = v___x_2923_;
v_isShared_2933_ = v_isSharedCheck_2956_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_snapshotTasks_2930_);
lean_inc(v_infoState_2929_);
lean_inc(v_messages_2928_);
lean_inc(v_traceState_2927_);
lean_inc(v_auxDeclNGen_2926_);
lean_inc(v_ngen_2925_);
lean_inc(v_nextMacroScope_2924_);
lean_dec(v___x_2923_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2956_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 5, v___x_2934_);
lean_ctor_set(v___x_2932_, 0, v_env_2919_);
v___x_2936_ = v___x_2932_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_env_2919_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_nextMacroScope_2924_);
lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_ngen_2925_);
lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_auxDeclNGen_2926_);
lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_traceState_2927_);
lean_ctor_set(v_reuseFailAlloc_2955_, 5, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2955_, 6, v_messages_2928_);
lean_ctor_set(v_reuseFailAlloc_2955_, 7, v_infoState_2929_);
lean_ctor_set(v_reuseFailAlloc_2955_, 8, v_snapshotTasks_2930_);
v___x_2936_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_mctx_2939_; lean_object* v_zetaDeltaFVarIds_2940_; lean_object* v_postponed_2941_; lean_object* v_diag_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2953_; 
v___x_2937_ = lean_st_ref_put(v___y_2921_, v___x_2936_);
v___x_2938_ = lean_st_ref_take(v___y_2920_);
v_mctx_2939_ = lean_ctor_get(v___x_2938_, 0);
v_zetaDeltaFVarIds_2940_ = lean_ctor_get(v___x_2938_, 2);
v_postponed_2941_ = lean_ctor_get(v___x_2938_, 3);
v_diag_2942_ = lean_ctor_get(v___x_2938_, 4);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v___x_2938_, 1);
lean_dec(v_unused_2954_);
v___x_2944_ = v___x_2938_;
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_diag_2942_);
lean_inc(v_postponed_2941_);
lean_inc(v_zetaDeltaFVarIds_2940_);
lean_inc(v_mctx_2939_);
lean_dec(v___x_2938_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_2946_);
v___x_2948_ = v___x_2944_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_mctx_2939_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_zetaDeltaFVarIds_2940_);
lean_ctor_set(v_reuseFailAlloc_2952_, 3, v_postponed_2941_);
lean_ctor_set(v_reuseFailAlloc_2952_, 4, v_diag_2942_);
v___x_2948_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_st_ref_put(v___y_2920_, v___x_2948_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2964_, lean_object* v_x_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; lean_object* v_env_2972_; lean_object* v_a_2974_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2971_ = lean_st_ref_get(v___y_2969_);
v_env_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc_ref(v_env_2972_);
lean_dec(v___x_2971_);
v___x_2984_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2964_, v___y_2967_, v___y_2969_);
lean_dec_ref(v___x_2984_);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___x_2985_ = lean_apply_5(v_x_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, lean_box(0));
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2972_, v___y_2967_, v___y_2969_);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v___x_2987_, 0);
lean_dec(v_unused_2995_);
v___x_2989_ = v___x_2987_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v___x_2987_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v_a_2986_);
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2986_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
else
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2985_, 1);
v_a_2974_ = v_a_2996_;
goto v___jp_2973_;
}
v___jp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v___x_2975_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2972_, v___y_2967_, v___y_2969_);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_2983_);
v___x_2977_ = v___x_2975_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_dec(v___x_2975_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 1);
lean_ctor_set(v___x_2977_, 0, v_a_2974_);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2974_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_2997_, lean_object* v_x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_2997_, v_x_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3005_, lean_object* v_argsPacker_3006_, lean_object* v_preDefs_3007_, lean_object* v_unaryPreDefNonRec_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3014_; lean_object* v_levelParams_3015_; lean_object* v_env_3016_; lean_object* v___x_3017_; lean_object* v_us_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3014_ = lean_st_ref_get(v_a_3012_);
v_levelParams_3015_ = lean_ctor_get(v_unaryPreDefNonRec_3008_, 1);
v_env_3016_ = lean_ctor_get(v___x_3014_, 0);
lean_inc_ref(v_env_3016_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
lean_inc(v_levelParams_3015_);
v_us_3018_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3015_, v___x_3017_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3019_, 0, v_unaryPreDefNonRec_3008_);
lean_closure_set(v___f_3019_, 1, v_preDefs_3007_);
lean_closure_set(v___f_3019_, 2, v_fixedParamPerms_3005_);
lean_closure_set(v___f_3019_, 3, v_us_3018_);
lean_closure_set(v___f_3019_, 4, v_argsPacker_3006_);
v___x_3020_ = l_Lean_Environment_unlockAsync(v_env_3016_);
v___x_3021_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3020_, v___f_3019_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3022_, lean_object* v_argsPacker_3023_, lean_object* v_preDefs_3024_, lean_object* v_unaryPreDefNonRec_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3022_, v_argsPacker_3023_, v_preDefs_3024_, v_unaryPreDefNonRec_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3032_, lean_object* v_unaryPreDefNonRec_3033_, lean_object* v_us_3034_, lean_object* v_argsPacker_3035_, lean_object* v_as_3036_, size_t v_sz_3037_, size_t v_i_3038_, lean_object* v_bs_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3032_, v_unaryPreDefNonRec_3033_, v_us_3034_, v_argsPacker_3035_, v_sz_3037_, v_i_3038_, v_bs_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3046_, lean_object* v_unaryPreDefNonRec_3047_, lean_object* v_us_3048_, lean_object* v_argsPacker_3049_, lean_object* v_as_3050_, lean_object* v_sz_3051_, lean_object* v_i_3052_, lean_object* v_bs_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
size_t v_sz_boxed_3059_; size_t v_i_boxed_3060_; lean_object* v_res_3061_; 
v_sz_boxed_3059_ = lean_unbox_usize(v_sz_3051_);
lean_dec(v_sz_3051_);
v_i_boxed_3060_ = lean_unbox_usize(v_i_3052_);
lean_dec(v_i_3052_);
v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3046_, v_unaryPreDefNonRec_3047_, v_us_3048_, v_argsPacker_3049_, v_as_3050_, v_sz_boxed_3059_, v_i_boxed_3060_, v_bs_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v_as_3050_);
lean_dec_ref(v_fixedParamPerms_3046_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3062_, v___y_3064_, v___y_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3076_, lean_object* v_env_3077_, lean_object* v_x_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3077_, v_x_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_env_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3085_, v_env_3086_, v_x_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3093_;
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
