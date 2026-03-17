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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object*);
uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.WF.preDefsFromUnaryNonRec"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: arity = params.size\n        "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__1_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
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
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
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
lean_dec_ref(v___x_148_);
v___x_150_ = 1;
v___x_151_ = 1;
v___x_152_ = l_Lean_Meta_mkLambdaFVars(v_xs_139_, v_a_149_, v___x_137_, v___x_150_, v___x_137_, v___x_150_, v___x_151_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v___x_152_;
}
else
{
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_withAppN___lam__0___boxed(lean_object* v_args_165_, lean_object* v_k_166_, lean_object* v___x_167_, lean_object* v_missing_168_, lean_object* v_xs_169_, lean_object* v_x_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v___x_2383__boxed_176_; lean_object* v_res_177_; 
v___x_2383__boxed_176_ = lean_unbox(v___x_167_);
v_res_177_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_165_, v_k_166_, v___x_2383__boxed_176_, v_missing_168_, v_xs_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
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
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
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
lean_object* v___f_260_; lean_object* v___x_1602__overap_261_; lean_object* v___x_262_; 
v___f_260_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1602__overap_261_ = lean_panic_fn(v___f_260_, v_msg_254_);
v___x_262_ = lean_apply_5(v___x_1602__overap_261_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_packCalls_spec__1___boxed(lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v_msg_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
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
lean_dec_ref(v_v_364_);
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
uint8_t v___x_10084__boxed_379_; size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v___x_10084__boxed_379_ = lean_unbox(v___x_375_);
v_sz_boxed_380_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_381_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_10084__boxed_379_, v_sz_boxed_380_, v_i_boxed_381_, v_bs_378_);
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
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
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
lean_inc(v___x_420_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_421_, 0, v___x_420_);
lean_closure_set(v___f_421_, 1, v_argsPacker_395_);
lean_closure_set(v___f_421_, 2, v___x_396_);
lean_closure_set(v___f_421_, 3, v_val_410_);
lean_closure_set(v___f_421_, 4, v_newF_397_);
v_sz_422_ = lean_array_size(v___x_420_);
v___x_423_ = ((size_t)0ULL);
lean_inc(v___x_420_);
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
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = l_Lean_maxRecDepthErrorMessage;
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__3);
v___x_486_ = l_Lean_MessageData_ofFormat(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__4);
v___x_488_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__2));
v___x_489_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(lean_object* v_ref_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___closed__5);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_ref_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg___boxed(lean_object* v_ref_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___y_506_; lean_object* v_fileName_515_; lean_object* v_fileMap_516_; lean_object* v_options_517_; lean_object* v_currRecDepth_518_; lean_object* v_maxRecDepth_519_; lean_object* v_ref_520_; lean_object* v_currNamespace_521_; lean_object* v_openDecls_522_; lean_object* v_initHeartbeats_523_; lean_object* v_maxHeartbeats_524_; lean_object* v_quotContext_525_; lean_object* v_currMacroScope_526_; uint8_t v_diag_527_; lean_object* v_cancelTk_x3f_528_; uint8_t v_suppressElabErrors_529_; lean_object* v_inheritedTraceOptions_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_542_; 
v_fileName_515_ = lean_ctor_get(v___y_502_, 0);
v_fileMap_516_ = lean_ctor_get(v___y_502_, 1);
v_options_517_ = lean_ctor_get(v___y_502_, 2);
v_currRecDepth_518_ = lean_ctor_get(v___y_502_, 3);
v_maxRecDepth_519_ = lean_ctor_get(v___y_502_, 4);
v_ref_520_ = lean_ctor_get(v___y_502_, 5);
v_currNamespace_521_ = lean_ctor_get(v___y_502_, 6);
v_openDecls_522_ = lean_ctor_get(v___y_502_, 7);
v_initHeartbeats_523_ = lean_ctor_get(v___y_502_, 8);
v_maxHeartbeats_524_ = lean_ctor_get(v___y_502_, 9);
v_quotContext_525_ = lean_ctor_get(v___y_502_, 10);
v_currMacroScope_526_ = lean_ctor_get(v___y_502_, 11);
v_diag_527_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*14);
v_cancelTk_x3f_528_ = lean_ctor_get(v___y_502_, 12);
v_suppressElabErrors_529_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_530_ = lean_ctor_get(v___y_502_, 13);
v_isSharedCheck_542_ = !lean_is_exclusive(v___y_502_);
if (v_isSharedCheck_542_ == 0)
{
v___x_532_ = v___y_502_;
v_isShared_533_ = v_isSharedCheck_542_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_inheritedTraceOptions_530_);
lean_inc(v_cancelTk_x3f_528_);
lean_inc(v_currMacroScope_526_);
lean_inc(v_quotContext_525_);
lean_inc(v_maxHeartbeats_524_);
lean_inc(v_initHeartbeats_523_);
lean_inc(v_openDecls_522_);
lean_inc(v_currNamespace_521_);
lean_inc(v_ref_520_);
lean_inc(v_maxRecDepth_519_);
lean_inc(v_currRecDepth_518_);
lean_inc(v_options_517_);
lean_inc(v_fileMap_516_);
lean_inc(v_fileName_515_);
lean_dec(v___y_502_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_542_;
goto v_resetjp_531_;
}
v___jp_505_:
{
if (lean_obj_tag(v___y_506_) == 0)
{
return v___y_506_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_507_ = lean_ctor_get(v___y_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___y_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___y_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___y_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
v_resetjp_531_:
{
uint8_t v___x_534_; 
v___x_534_ = lean_nat_dec_eq(v_currRecDepth_518_, v_maxRecDepth_519_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_currRecDepth_518_, v___x_535_);
lean_dec(v_currRecDepth_518_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 3, v___x_536_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fileName_515_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_fileMap_516_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_options_517_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v_maxRecDepth_519_);
lean_ctor_set(v_reuseFailAlloc_540_, 5, v_ref_520_);
lean_ctor_set(v_reuseFailAlloc_540_, 6, v_currNamespace_521_);
lean_ctor_set(v_reuseFailAlloc_540_, 7, v_openDecls_522_);
lean_ctor_set(v_reuseFailAlloc_540_, 8, v_initHeartbeats_523_);
lean_ctor_set(v_reuseFailAlloc_540_, 9, v_maxHeartbeats_524_);
lean_ctor_set(v_reuseFailAlloc_540_, 10, v_quotContext_525_);
lean_ctor_set(v_reuseFailAlloc_540_, 11, v_currMacroScope_526_);
lean_ctor_set(v_reuseFailAlloc_540_, 12, v_cancelTk_x3f_528_);
lean_ctor_set(v_reuseFailAlloc_540_, 13, v_inheritedTraceOptions_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, sizeof(void*)*14, v_diag_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, sizeof(void*)*14 + 1, v_suppressElabErrors_529_);
v___x_538_ = v_reuseFailAlloc_540_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_apply_6(v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___x_538_, v___y_503_, lean_box(0));
v___y_506_ = v___x_539_;
goto v___jp_505_;
}
}
else
{
lean_object* v___x_541_; 
lean_del_object(v___x_532_);
lean_dec_ref(v_inheritedTraceOptions_530_);
lean_dec(v_cancelTk_x3f_528_);
lean_dec(v_currMacroScope_526_);
lean_dec(v_quotContext_525_);
lean_dec(v_maxHeartbeats_524_);
lean_dec(v_initHeartbeats_523_);
lean_dec(v_openDecls_522_);
lean_dec(v_currNamespace_521_);
lean_dec(v_maxRecDepth_519_);
lean_dec(v_currRecDepth_518_);
lean_dec_ref(v_options_517_);
lean_dec_ref(v_fileMap_516_);
lean_dec_ref(v_fileName_515_);
lean_dec(v___y_503_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v_x_498_);
v___x_541_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_520_);
v___y_506_ = v___x_541_;
goto v___jp_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_551_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_565_, lean_object* v___y_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_apply_7(v_k_565_, v_b_567_, v___y_566_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_574_, lean_object* v___y_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_574_, v___y_575_, v_b_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_583_, lean_object* v_type_584_, lean_object* v_val_585_, lean_object* v_k_586_, uint8_t v_nondep_587_, uint8_t v_kind_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___f_595_; lean_object* v___x_596_; 
v___f_595_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_595_, 0, v_k_586_);
lean_closure_set(v___f_595_, 1, v___y_589_);
v___x_596_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_583_, v_type_584_, v_val_585_, v___f_595_, v_nondep_587_, v_kind_588_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_596_) == 0)
{
return v___x_596_;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_605_, lean_object* v_type_606_, lean_object* v_val_607_, lean_object* v_k_608_, lean_object* v_nondep_609_, lean_object* v_kind_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v_nondep_boxed_617_; uint8_t v_kind_boxed_618_; lean_object* v_res_619_; 
v_nondep_boxed_617_ = lean_unbox(v_nondep_609_);
v_kind_boxed_618_ = lean_unbox(v_kind_610_);
v_res_619_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_605_, v_type_606_, v_val_607_, v_k_608_, v_nondep_boxed_617_, v_kind_boxed_618_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_620_, uint8_t v_bi_621_, lean_object* v_type_622_, lean_object* v_k_623_, uint8_t v_kind_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___f_631_; lean_object* v___x_632_; 
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_631_, 0, v_k_623_);
lean_closure_set(v___f_631_, 1, v___y_625_);
v___x_632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_620_, v_bi_621_, v_type_622_, v___f_631_, v_kind_624_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_632_) == 0)
{
return v___x_632_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_641_, lean_object* v_bi_642_, lean_object* v_type_643_, lean_object* v_k_644_, lean_object* v_kind_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v_bi_boxed_652_; uint8_t v_kind_boxed_653_; lean_object* v_res_654_; 
v_bi_boxed_652_ = lean_unbox(v_bi_642_);
v_kind_boxed_653_ = lean_unbox(v_kind_645_);
v_res_654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_641_, v_bi_boxed_652_, v_type_643_, v_k_644_, v_kind_boxed_653_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_655_, lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_apply_1(v_x_656_, lean_box(0));
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_664_, v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_box(0);
return v___x_674_;
}
else
{
lean_object* v_key_675_; lean_object* v_value_676_; lean_object* v_tail_677_; uint8_t v___x_678_; 
v_key_675_ = lean_ctor_get(v_x_673_, 0);
v_value_676_ = lean_ctor_get(v_x_673_, 1);
v_tail_677_ = lean_ctor_get(v_x_673_, 2);
v___x_678_ = l_Lean_ExprStructEq_beq(v_key_675_, v_a_672_);
if (v___x_678_ == 0)
{
v_x_673_ = v_tail_677_;
goto _start;
}
else
{
lean_object* v___x_680_; 
lean_inc(v_value_676_);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_value_676_);
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_681_, v_x_682_);
lean_dec(v_x_682_);
lean_dec_ref(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_buckets_686_; lean_object* v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v_fold_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_buckets_686_ = lean_ctor_get(v_m_684_, 1);
v___x_687_ = lean_array_get_size(v_buckets_686_);
v___x_688_ = l_Lean_ExprStructEq_hash(v_a_685_);
v___x_689_ = 32ULL;
v___x_690_ = lean_uint64_shift_right(v___x_688_, v___x_689_);
v_fold_691_ = lean_uint64_xor(v___x_688_, v___x_690_);
v___x_692_ = 16ULL;
v___x_693_ = lean_uint64_shift_right(v_fold_691_, v___x_692_);
v___x_694_ = lean_uint64_xor(v_fold_691_, v___x_693_);
v___x_695_ = lean_uint64_to_usize(v___x_694_);
v___x_696_ = lean_usize_of_nat(v___x_687_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_sub(v___x_696_, v___x_697_);
v___x_699_ = lean_usize_land(v___x_695_, v___x_698_);
v___x_700_ = lean_array_uget_borrowed(v_buckets_686_, v___x_699_);
v___x_701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_685_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_702_, v_a_703_);
lean_dec_ref(v_a_703_);
lean_dec_ref(v_m_702_);
return v_res_704_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
else
{
lean_object* v_key_708_; lean_object* v_tail_709_; uint8_t v___x_710_; 
v_key_708_ = lean_ctor_get(v_x_706_, 0);
v_tail_709_ = lean_ctor_get(v_x_706_, 2);
v___x_710_ = l_Lean_ExprStructEq_beq(v_key_708_, v_a_705_);
if (v___x_710_ == 0)
{
v_x_706_ = v_tail_709_;
goto _start;
}
else
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_712_, lean_object* v_x_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_712_, v_x_713_);
lean_dec(v_x_713_);
lean_dec_ref(v_a_712_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_717_) == 0)
{
return v_x_716_;
}
else
{
lean_object* v_key_718_; lean_object* v_value_719_; lean_object* v_tail_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_743_; 
v_key_718_ = lean_ctor_get(v_x_717_, 0);
v_value_719_ = lean_ctor_get(v_x_717_, 1);
v_tail_720_ = lean_ctor_get(v_x_717_, 2);
v_isSharedCheck_743_ = !lean_is_exclusive(v_x_717_);
if (v_isSharedCheck_743_ == 0)
{
v___x_722_ = v_x_717_;
v_isShared_723_ = v_isSharedCheck_743_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_tail_720_);
lean_inc(v_value_719_);
lean_inc(v_key_718_);
lean_dec(v_x_717_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_743_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v_fold_728_; uint64_t v___x_729_; uint64_t v___x_730_; uint64_t v___x_731_; size_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_724_ = lean_array_get_size(v_x_716_);
v___x_725_ = l_Lean_ExprStructEq_hash(v_key_718_);
v___x_726_ = 32ULL;
v___x_727_ = lean_uint64_shift_right(v___x_725_, v___x_726_);
v_fold_728_ = lean_uint64_xor(v___x_725_, v___x_727_);
v___x_729_ = 16ULL;
v___x_730_ = lean_uint64_shift_right(v_fold_728_, v___x_729_);
v___x_731_ = lean_uint64_xor(v_fold_728_, v___x_730_);
v___x_732_ = lean_uint64_to_usize(v___x_731_);
v___x_733_ = lean_usize_of_nat(v___x_724_);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_sub(v___x_733_, v___x_734_);
v___x_736_ = lean_usize_land(v___x_732_, v___x_735_);
v___x_737_ = lean_array_uget_borrowed(v_x_716_, v___x_736_);
lean_inc(v___x_737_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 2, v___x_737_);
v___x_739_ = v___x_722_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_key_718_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_value_719_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v___x_737_);
v___x_739_ = v_reuseFailAlloc_742_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; 
v___x_740_ = lean_array_uset(v_x_716_, v___x_736_, v___x_739_);
v_x_716_ = v___x_740_;
v_x_717_ = v_tail_720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_744_, lean_object* v_source_745_, lean_object* v_target_746_){
_start:
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = lean_array_get_size(v_source_745_);
v___x_748_ = lean_nat_dec_lt(v_i_744_, v___x_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v_source_745_);
lean_dec(v_i_744_);
return v_target_746_;
}
else
{
lean_object* v_es_749_; lean_object* v___x_750_; lean_object* v_source_751_; lean_object* v_target_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_es_749_ = lean_array_fget(v_source_745_, v_i_744_);
v___x_750_ = lean_box(0);
v_source_751_ = lean_array_fset(v_source_745_, v_i_744_, v___x_750_);
v_target_752_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_746_, v_es_749_);
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_i_744_, v___x_753_);
lean_dec(v_i_744_);
v_i_744_ = v___x_754_;
v_source_745_ = v_source_751_;
v_target_746_ = v_target_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_nbuckets_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = lean_array_get_size(v_data_756_);
v___x_758_ = lean_unsigned_to_nat(2u);
v_nbuckets_759_ = lean_nat_mul(v___x_757_, v___x_758_);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_box(0);
v___x_762_ = lean_mk_array(v_nbuckets_759_, v___x_761_);
v___x_763_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_760_, v_data_756_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_764_, lean_object* v_b_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_dec(v_b_765_);
lean_dec_ref(v_a_764_);
return v_x_766_;
}
else
{
lean_object* v_key_767_; lean_object* v_value_768_; lean_object* v_tail_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_781_; 
v_key_767_ = lean_ctor_get(v_x_766_, 0);
v_value_768_ = lean_ctor_get(v_x_766_, 1);
v_tail_769_ = lean_ctor_get(v_x_766_, 2);
v_isSharedCheck_781_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_781_ == 0)
{
v___x_771_ = v_x_766_;
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_tail_769_);
lean_inc(v_value_768_);
lean_inc(v_key_767_);
lean_dec(v_x_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_781_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
uint8_t v___x_773_; 
v___x_773_ = l_Lean_ExprStructEq_beq(v_key_767_, v_a_764_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_764_, v_b_765_, v_tail_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 2, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_key_767_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_value_768_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v___x_779_; 
lean_dec(v_value_768_);
lean_dec(v_key_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_b_765_);
lean_ctor_set(v___x_771_, 0, v_a_764_);
v___x_779_ = v___x_771_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_b_765_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_tail_769_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_782_, lean_object* v_a_783_, lean_object* v_b_784_){
_start:
{
lean_object* v_size_785_; lean_object* v_buckets_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_829_; 
v_size_785_ = lean_ctor_get(v_m_782_, 0);
v_buckets_786_ = lean_ctor_get(v_m_782_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_m_782_);
if (v_isSharedCheck_829_ == 0)
{
v___x_788_ = v_m_782_;
v_isShared_789_ = v_isSharedCheck_829_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_buckets_786_);
lean_inc(v_size_785_);
lean_dec(v_m_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_829_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v_fold_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v_bkt_803_; uint8_t v___x_804_; 
v___x_790_ = lean_array_get_size(v_buckets_786_);
v___x_791_ = l_Lean_ExprStructEq_hash(v_a_783_);
v___x_792_ = 32ULL;
v___x_793_ = lean_uint64_shift_right(v___x_791_, v___x_792_);
v_fold_794_ = lean_uint64_xor(v___x_791_, v___x_793_);
v___x_795_ = 16ULL;
v___x_796_ = lean_uint64_shift_right(v_fold_794_, v___x_795_);
v___x_797_ = lean_uint64_xor(v_fold_794_, v___x_796_);
v___x_798_ = lean_uint64_to_usize(v___x_797_);
v___x_799_ = lean_usize_of_nat(v___x_790_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_sub(v___x_799_, v___x_800_);
v___x_802_ = lean_usize_land(v___x_798_, v___x_801_);
v_bkt_803_ = lean_array_uget_borrowed(v_buckets_786_, v___x_802_);
v___x_804_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_783_, v_bkt_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v_size_x27_806_; lean_object* v___x_807_; lean_object* v_buckets_x27_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_805_ = lean_unsigned_to_nat(1u);
v_size_x27_806_ = lean_nat_add(v_size_785_, v___x_805_);
lean_dec(v_size_785_);
lean_inc(v_bkt_803_);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v_a_783_);
lean_ctor_set(v___x_807_, 1, v_b_784_);
lean_ctor_set(v___x_807_, 2, v_bkt_803_);
v_buckets_x27_808_ = lean_array_uset(v_buckets_786_, v___x_802_, v___x_807_);
v___x_809_ = lean_unsigned_to_nat(4u);
v___x_810_ = lean_nat_mul(v_size_x27_806_, v___x_809_);
v___x_811_ = lean_unsigned_to_nat(3u);
v___x_812_ = lean_nat_div(v___x_810_, v___x_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_array_get_size(v_buckets_x27_808_);
v___x_814_ = lean_nat_dec_le(v___x_812_, v___x_813_);
lean_dec(v___x_812_);
if (v___x_814_ == 0)
{
lean_object* v_val_815_; lean_object* v___x_817_; 
v_val_815_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_808_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_val_815_);
lean_ctor_set(v___x_788_, 0, v_size_x27_806_);
v___x_817_ = v___x_788_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_size_x27_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_val_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v___x_820_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_buckets_x27_808_);
lean_ctor_set(v___x_788_, 0, v_size_x27_806_);
v___x_820_ = v___x_788_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_size_x27_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_buckets_x27_808_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v___x_822_; lean_object* v_buckets_x27_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
lean_inc(v_bkt_803_);
v___x_822_ = lean_box(0);
v_buckets_x27_823_ = lean_array_uset(v_buckets_786_, v___x_802_, v___x_822_);
v___x_824_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_783_, v_b_784_, v_bkt_803_);
v___x_825_ = lean_array_uset(v_buckets_x27_823_, v___x_802_, v___x_824_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_825_);
v___x_827_ = v___x_788_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_size_785_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_830_, lean_object* v_e_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_834_ = lean_st_ref_take(v_a_830_);
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_834_, v_e_831_, v_a_832_);
v___x_836_ = lean_st_ref_set(v_a_830_, v___x_835_);
v___x_837_ = lean_box(0);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_838_, lean_object* v_e_839_, lean_object* v_a_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_838_, v_e_839_, v_a_840_);
lean_dec(v_a_838_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_845_, lean_object* v_pre_846_, lean_object* v_post_847_, uint8_t v_usedLetOnly_848_, uint8_t v_skipConstInApp_849_, uint8_t v_skipInstances_850_, lean_object* v_body_851_, lean_object* v_x_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_array_push(v_fvars_845_, v_x_852_);
v___x_860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_846_, v_post_847_, v_usedLetOnly_848_, v_skipConstInApp_849_, v_skipInstances_850_, v___x_859_, v_body_851_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_861_, lean_object* v_pre_862_, lean_object* v_post_863_, lean_object* v_usedLetOnly_864_, lean_object* v_skipConstInApp_865_, lean_object* v_skipInstances_866_, lean_object* v_body_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_usedLetOnly_boxed_875_; uint8_t v_skipConstInApp_boxed_876_; uint8_t v_skipInstances_boxed_877_; lean_object* v_res_878_; 
v_usedLetOnly_boxed_875_ = lean_unbox(v_usedLetOnly_864_);
v_skipConstInApp_boxed_876_ = lean_unbox(v_skipConstInApp_865_);
v_skipInstances_boxed_877_ = lean_unbox(v_skipInstances_866_);
v_res_878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_861_, v_pre_862_, v_post_863_, v_usedLetOnly_boxed_875_, v_skipConstInApp_boxed_876_, v_skipInstances_boxed_877_, v_body_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_879_, lean_object* v_post_880_, uint8_t v_usedLetOnly_881_, uint8_t v_skipConstInApp_882_, uint8_t v_skipInstances_883_, lean_object* v_e_884_, lean_object* v_a_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
lean_inc_ref(v_post_880_);
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc_ref(v_e_884_);
v___x_891_ = lean_apply_6(v_post_880_, v_e_884_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_910_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_910_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_910_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_910_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
switch(lean_obj_tag(v_a_892_))
{
case 0:
{
lean_object* v_e_896_; lean_object* v___x_898_; 
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_e_884_);
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_e_896_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_e_896_);
lean_dec_ref(v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_e_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_e_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
case 1:
{
lean_object* v_e_900_; lean_object* v___x_901_; 
lean_del_object(v___x_894_);
lean_dec_ref(v_e_884_);
v_e_900_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_e_900_);
lean_dec_ref(v_a_892_);
v___x_901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_879_, v_post_880_, v_usedLetOnly_881_, v_skipConstInApp_882_, v_skipInstances_883_, v_e_900_, v_a_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_901_;
}
default: 
{
lean_object* v_e_x3f_902_; 
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_e_x3f_902_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_e_x3f_902_);
lean_dec_ref(v_a_892_);
if (lean_obj_tag(v_e_x3f_902_) == 0)
{
lean_object* v___x_904_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_e_884_);
v___x_904_ = v___x_894_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_e_884_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
else
{
lean_object* v_val_906_; lean_object* v___x_908_; 
lean_dec_ref(v_e_884_);
v_val_906_ = lean_ctor_get(v_e_x3f_902_, 0);
lean_inc(v_val_906_);
lean_dec_ref(v_e_x3f_902_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_val_906_);
v___x_908_ = v___x_894_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_val_906_);
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
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_e_884_);
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_a_911_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_891_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_891_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_919_, lean_object* v_post_920_, uint8_t v_usedLetOnly_921_, uint8_t v_skipConstInApp_922_, uint8_t v_skipInstances_923_, lean_object* v_fvars_924_, lean_object* v_e_925_, lean_object* v_a_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
if (lean_obj_tag(v_e_925_) == 6)
{
lean_object* v_binderName_932_; lean_object* v_binderType_933_; lean_object* v_body_934_; uint8_t v_binderInfo_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_binderName_932_ = lean_ctor_get(v_e_925_, 0);
lean_inc(v_binderName_932_);
v_binderType_933_ = lean_ctor_get(v_e_925_, 1);
lean_inc_ref(v_binderType_933_);
v_body_934_ = lean_ctor_get(v_e_925_, 2);
lean_inc_ref(v_body_934_);
v_binderInfo_935_ = lean_ctor_get_uint8(v_e_925_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_925_);
v___x_936_ = lean_expr_instantiate_rev(v_binderType_933_, v_fvars_924_);
lean_dec_ref(v_binderType_933_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v_a_926_);
lean_inc_ref(v_post_920_);
lean_inc_ref(v_pre_919_);
v___x_937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_919_, v_post_920_, v_usedLetOnly_921_, v_skipConstInApp_922_, v_skipInstances_923_, v___x_936_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___f_942_; uint8_t v___x_943_; lean_object* v___x_944_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_937_);
v___x_939_ = lean_box(v_usedLetOnly_921_);
v___x_940_ = lean_box(v_skipConstInApp_922_);
v___x_941_ = lean_box(v_skipInstances_923_);
v___f_942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_942_, 0, v_fvars_924_);
lean_closure_set(v___f_942_, 1, v_pre_919_);
lean_closure_set(v___f_942_, 2, v_post_920_);
lean_closure_set(v___f_942_, 3, v___x_939_);
lean_closure_set(v___f_942_, 4, v___x_940_);
lean_closure_set(v___f_942_, 5, v___x_941_);
lean_closure_set(v___f_942_, 6, v_body_934_);
v___x_943_ = 0;
v___x_944_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_932_, v_binderInfo_935_, v_a_938_, v___f_942_, v___x_943_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_944_;
}
else
{
lean_dec_ref(v_body_934_);
lean_dec(v_binderName_932_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_fvars_924_);
lean_dec_ref(v_post_920_);
lean_dec_ref(v_pre_919_);
return v___x_937_;
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_expr_instantiate_rev(v_e_925_, v_fvars_924_);
lean_dec_ref(v_e_925_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v_a_926_);
lean_inc_ref(v_post_920_);
lean_inc_ref(v_pre_919_);
v___x_946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_919_, v_post_920_, v_usedLetOnly_921_, v_skipConstInApp_922_, v_skipInstances_923_, v___x_945_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
v___x_948_ = 0;
v___x_949_ = 1;
v___x_950_ = 1;
v___x_951_ = l_Lean_Meta_mkLambdaFVars(v_fvars_924_, v_a_947_, v___x_948_, v_usedLetOnly_921_, v___x_948_, v___x_949_, v___x_950_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec_ref(v_fvars_924_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v___x_951_);
v___x_953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_919_, v_post_920_, v_usedLetOnly_921_, v_skipConstInApp_922_, v_skipInstances_923_, v_a_952_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_953_;
}
else
{
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_post_920_);
lean_dec_ref(v_pre_919_);
return v___x_951_;
}
}
else
{
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_fvars_924_);
lean_dec_ref(v_post_920_);
lean_dec_ref(v_pre_919_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_954_, lean_object* v_pre_955_, lean_object* v_post_956_, uint8_t v_usedLetOnly_957_, uint8_t v_skipConstInApp_958_, uint8_t v_skipInstances_959_, lean_object* v_body_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_array_push(v_fvars_954_, v_x_961_);
v___x_969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_955_, v_post_956_, v_usedLetOnly_957_, v_skipConstInApp_958_, v_skipInstances_959_, v___x_968_, v_body_960_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_970_, lean_object* v_pre_971_, lean_object* v_post_972_, lean_object* v_usedLetOnly_973_, lean_object* v_skipConstInApp_974_, lean_object* v_skipInstances_975_, lean_object* v_body_976_, lean_object* v_x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v_usedLetOnly_boxed_984_; uint8_t v_skipConstInApp_boxed_985_; uint8_t v_skipInstances_boxed_986_; lean_object* v_res_987_; 
v_usedLetOnly_boxed_984_ = lean_unbox(v_usedLetOnly_973_);
v_skipConstInApp_boxed_985_ = lean_unbox(v_skipConstInApp_974_);
v_skipInstances_boxed_986_ = lean_unbox(v_skipInstances_975_);
v_res_987_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_970_, v_pre_971_, v_post_972_, v_usedLetOnly_boxed_984_, v_skipConstInApp_boxed_985_, v_skipInstances_boxed_986_, v_body_976_, v_x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_988_, lean_object* v_post_989_, uint8_t v_usedLetOnly_990_, uint8_t v_skipConstInApp_991_, uint8_t v_skipInstances_992_, lean_object* v_fvars_993_, lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
if (lean_obj_tag(v_e_994_) == 8)
{
lean_object* v_declName_1001_; lean_object* v_type_1002_; lean_object* v_value_1003_; lean_object* v_body_1004_; uint8_t v_nondep_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_declName_1001_ = lean_ctor_get(v_e_994_, 0);
lean_inc(v_declName_1001_);
v_type_1002_ = lean_ctor_get(v_e_994_, 1);
lean_inc_ref(v_type_1002_);
v_value_1003_ = lean_ctor_get(v_e_994_, 2);
lean_inc_ref(v_value_1003_);
v_body_1004_ = lean_ctor_get(v_e_994_, 3);
lean_inc_ref(v_body_1004_);
v_nondep_1005_ = lean_ctor_get_uint8(v_e_994_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_994_);
v___x_1006_ = lean_expr_instantiate_rev(v_type_1002_, v_fvars_993_);
lean_dec_ref(v_type_1002_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v_a_995_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1006_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = lean_expr_instantiate_rev(v_value_1003_, v_fvars_993_);
lean_dec_ref(v_value_1003_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v_a_995_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1009_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref(v___x_1010_);
v___x_1012_ = lean_box(v_usedLetOnly_990_);
v___x_1013_ = lean_box(v_skipConstInApp_991_);
v___x_1014_ = lean_box(v_skipInstances_992_);
v___f_1015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1015_, 0, v_fvars_993_);
lean_closure_set(v___f_1015_, 1, v_pre_988_);
lean_closure_set(v___f_1015_, 2, v_post_989_);
lean_closure_set(v___f_1015_, 3, v___x_1012_);
lean_closure_set(v___f_1015_, 4, v___x_1013_);
lean_closure_set(v___f_1015_, 5, v___x_1014_);
lean_closure_set(v___f_1015_, 6, v_body_1004_);
v___x_1016_ = 0;
v___x_1017_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_1001_, v_a_1008_, v_a_1011_, v___f_1015_, v_nondep_1005_, v___x_1016_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1017_;
}
else
{
lean_dec(v_a_1008_);
lean_dec_ref(v_body_1004_);
lean_dec(v_declName_1001_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1010_;
}
}
else
{
lean_dec_ref(v_body_1004_);
lean_dec_ref(v_value_1003_);
lean_dec(v_declName_1001_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1007_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_expr_instantiate_rev(v_e_994_, v_fvars_993_);
lean_dec_ref(v_e_994_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v_a_995_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1018_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; uint8_t v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = 0;
v___x_1022_ = 1;
v___x_1023_ = l_Lean_Meta_mkLetFVars(v_fvars_993_, v_a_1020_, v_usedLetOnly_990_, v___x_1021_, v___x_1022_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec_ref(v_fvars_993_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v_a_1024_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1025_;
}
else
{
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1023_;
}
}
else
{
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1026_, lean_object* v_post_1027_, uint8_t v_usedLetOnly_1028_, uint8_t v_skipConstInApp_1029_, uint8_t v_skipInstances_1030_, size_t v_sz_1031_, size_t v_i_1032_, lean_object* v_bs_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_lt(v_i_1032_, v_sz_1031_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v_post_1027_);
lean_dec_ref(v_pre_1026_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_bs_1033_);
return v___x_1041_;
}
else
{
lean_object* v_v_1042_; lean_object* v___x_1043_; 
v_v_1042_ = lean_array_uget_borrowed(v_bs_1033_, v_i_1032_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc(v_v_1042_);
lean_inc_ref(v_post_1027_);
lean_inc_ref(v_pre_1026_);
v___x_1043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1026_, v_post_1027_, v_usedLetOnly_1028_, v_skipConstInApp_1029_, v_skipInstances_1030_, v_v_1042_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v_bs_x27_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v_bs_x27_1046_ = lean_array_uset(v_bs_1033_, v_i_1032_, v___x_1045_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1032_, v___x_1047_);
v___x_1049_ = lean_array_uset(v_bs_x27_1046_, v_i_1032_, v_a_1044_);
v_i_1032_ = v___x_1048_;
v_bs_1033_ = v___x_1049_;
goto _start;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v_bs_1033_);
lean_dec_ref(v_post_1027_);
lean_dec_ref(v_pre_1026_);
v_a_1051_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1043_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1059_, lean_object* v_post_1060_, uint8_t v_usedLetOnly_1061_, uint8_t v_skipConstInApp_1062_, uint8_t v_skipInstances_1063_, lean_object* v___x_1064_, lean_object* v___y_1065_, lean_object* v_b_1066_, lean_object* v_a_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1059_, v_post_1060_, v_usedLetOnly_1061_, v_skipConstInApp_1062_, v_skipInstances_1063_, v___x_1064_, v___y_1065_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1083_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1078_ = lean_array_fset(v_b_1066_, v_a_1067_, v_a_1074_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1079_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_b_1066_);
v_a_1084_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1073_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1073_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1092_, lean_object* v_post_1093_, lean_object* v_usedLetOnly_1094_, lean_object* v_skipConstInApp_1095_, lean_object* v_skipInstances_1096_, lean_object* v___x_1097_, lean_object* v___y_1098_, lean_object* v_b_1099_, lean_object* v_a_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_usedLetOnly_boxed_1106_; uint8_t v_skipConstInApp_boxed_1107_; uint8_t v_skipInstances_boxed_1108_; lean_object* v_res_1109_; 
v_usedLetOnly_boxed_1106_ = lean_unbox(v_usedLetOnly_1094_);
v_skipConstInApp_boxed_1107_ = lean_unbox(v_skipConstInApp_1095_);
v_skipInstances_boxed_1108_ = lean_unbox(v_skipInstances_1096_);
v_res_1109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1092_, v_post_1093_, v_usedLetOnly_boxed_1106_, v_skipConstInApp_boxed_1107_, v_skipInstances_boxed_1108_, v___x_1097_, v___y_1098_, v_b_1099_, v_a_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v_a_1100_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1110_, lean_object* v___x_1111_, lean_object* v_pre_1112_, lean_object* v_post_1113_, uint8_t v_usedLetOnly_1114_, uint8_t v_skipConstInApp_1115_, uint8_t v_skipInstances_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___y_1126_; uint8_t v___x_1149_; 
v___x_1149_ = lean_nat_dec_lt(v_a_1117_, v_upperBound_1110_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v_a_1117_);
lean_dec_ref(v_post_1113_);
lean_dec_ref(v_pre_1112_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_b_1118_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = lean_array_fget_borrowed(v_b_1118_, v_a_1117_);
v___x_1152_ = lean_array_get_size(v___x_1111_);
v___x_1153_ = lean_nat_dec_lt(v_a_1117_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; 
lean_inc(v___x_1151_);
v___x_1154_ = lean_box(v_usedLetOnly_1114_);
v___x_1155_ = lean_box(v_skipConstInApp_1115_);
v___x_1156_ = lean_box(v_skipInstances_1116_);
lean_inc(v_a_1117_);
lean_inc(v___y_1119_);
lean_inc_ref(v_post_1113_);
lean_inc_ref(v_pre_1112_);
v___f_1157_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1157_, 0, v_pre_1112_);
lean_closure_set(v___f_1157_, 1, v_post_1113_);
lean_closure_set(v___f_1157_, 2, v___x_1154_);
lean_closure_set(v___f_1157_, 3, v___x_1155_);
lean_closure_set(v___f_1157_, 4, v___x_1156_);
lean_closure_set(v___f_1157_, 5, v___x_1151_);
lean_closure_set(v___f_1157_, 6, v___y_1119_);
lean_closure_set(v___f_1157_, 7, v_b_1118_);
lean_closure_set(v___f_1157_, 8, v_a_1117_);
v___y_1126_ = v___f_1157_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1158_; uint8_t v_isInstance_1159_; 
v___x_1158_ = lean_array_fget_borrowed(v___x_1111_, v_a_1117_);
v_isInstance_1159_ = lean_ctor_get_uint8(v___x_1158_, sizeof(void*)*1 + 4);
if (v_isInstance_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; 
lean_inc(v___x_1151_);
v___x_1160_ = lean_box(v_usedLetOnly_1114_);
v___x_1161_ = lean_box(v_skipConstInApp_1115_);
v___x_1162_ = lean_box(v_skipInstances_1116_);
lean_inc(v_a_1117_);
lean_inc(v___y_1119_);
lean_inc_ref(v_post_1113_);
lean_inc_ref(v_pre_1112_);
v___f_1163_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1163_, 0, v_pre_1112_);
lean_closure_set(v___f_1163_, 1, v_post_1113_);
lean_closure_set(v___f_1163_, 2, v___x_1160_);
lean_closure_set(v___f_1163_, 3, v___x_1161_);
lean_closure_set(v___f_1163_, 4, v___x_1162_);
lean_closure_set(v___f_1163_, 5, v___x_1151_);
lean_closure_set(v___f_1163_, 6, v___y_1119_);
lean_closure_set(v___f_1163_, 7, v_b_1118_);
lean_closure_set(v___f_1163_, 8, v_a_1117_);
v___y_1126_ = v___f_1163_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1164_; lean_object* v___f_1165_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1118_);
v___f_1165_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1165_, 0, v___x_1164_);
v___y_1126_ = v___f_1165_;
goto v___jp_1125_;
}
}
}
v___jp_1125_:
{
lean_object* v___x_1127_; 
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
v___x_1127_ = lean_apply_5(v___y_1126_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, lean_box(0));
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1140_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
if (lean_obj_tag(v_a_1128_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; 
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v_a_1117_);
lean_dec_ref(v_post_1113_);
lean_dec_ref(v_pre_1112_);
v_a_1132_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v_a_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_a_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1130_);
v_a_1136_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v_a_1128_);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_a_1117_, v___x_1137_);
lean_dec(v_a_1117_);
v_a_1117_ = v___x_1138_;
v_b_1118_ = v_a_1136_;
goto _start;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v_a_1117_);
lean_dec_ref(v_post_1113_);
lean_dec_ref(v_pre_1112_);
v_a_1141_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1127_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1166_, lean_object* v_pre_1167_, lean_object* v_post_1168_, uint8_t v_usedLetOnly_1169_, uint8_t v_skipConstInApp_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_f_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; 
if (lean_obj_tag(v_x_1171_) == 5)
{
lean_object* v_fn_1229_; lean_object* v_arg_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_fn_1229_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_fn_1229_);
v_arg_1230_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_arg_1230_);
lean_dec_ref(v_x_1171_);
v___x_1231_ = lean_array_set(v_x_1172_, v_x_1173_, v_arg_1230_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_sub(v_x_1173_, v___x_1232_);
lean_dec(v_x_1173_);
v_x_1171_ = v_fn_1229_;
v_x_1172_ = v___x_1231_;
v_x_1173_ = v___x_1233_;
goto _start;
}
else
{
lean_dec(v_x_1173_);
if (v_skipConstInApp_1170_ == 0)
{
goto v___jp_1226_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Lean_Expr_isConst(v_x_1171_);
if (v___x_1235_ == 0)
{
goto v___jp_1226_;
}
else
{
v_f_1181_ = v_x_1171_;
v___y_1182_ = v___y_1174_;
v___y_1183_ = v___y_1175_;
v___y_1184_ = v___y_1176_;
v___y_1185_ = v___y_1177_;
v___y_1186_ = v___y_1178_;
goto v___jp_1180_;
}
}
}
v___jp_1180_:
{
if (v_skipInstances_1166_ == 0)
{
size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v_sz_1187_ = lean_array_size(v_x_1172_);
v___x_1188_ = ((size_t)0ULL);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc(v___y_1182_);
lean_inc_ref(v_post_1168_);
lean_inc_ref(v_pre_1167_);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v_sz_1187_, v___x_1188_, v_x_1172_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v___x_1189_);
v___x_1191_ = l_Lean_mkAppN(v_f_1181_, v_a_1190_);
lean_dec(v_a_1190_);
v___x_1192_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v___x_1191_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v_f_1181_);
lean_dec_ref(v_post_1168_);
lean_dec_ref(v_pre_1167_);
v_a_1193_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1189_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1189_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_array_get_size(v_x_1172_);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc_ref(v_f_1181_);
v___x_1202_ = l_Lean_Meta_getFunInfoNArgs(v_f_1181_, v___x_1201_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_paramInfo_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref(v___x_1202_);
v_paramInfo_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc_ref(v_paramInfo_1204_);
lean_dec(v_a_1203_);
v___x_1205_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc(v___y_1182_);
lean_inc_ref(v_post_1168_);
lean_inc_ref(v_pre_1167_);
v___x_1206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1201_, v_paramInfo_1204_, v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v___x_1205_, v_x_1172_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec_ref(v_paramInfo_1204_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = l_Lean_mkAppN(v_f_1181_, v_a_1207_);
lean_dec(v_a_1207_);
v___x_1209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v___x_1208_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1209_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v_f_1181_);
lean_dec_ref(v_post_1168_);
lean_dec_ref(v_pre_1167_);
v_a_1210_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1206_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1206_);
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
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v_f_1181_);
lean_dec_ref(v_x_1172_);
lean_dec_ref(v_post_1168_);
lean_dec_ref(v_pre_1167_);
v_a_1218_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1202_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1202_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
v___jp_1226_:
{
lean_object* v___x_1227_; 
lean_inc(v___y_1178_);
lean_inc_ref(v___y_1177_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
lean_inc(v___y_1174_);
lean_inc_ref(v_post_1168_);
lean_inc_ref(v_pre_1167_);
v___x_1227_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v_x_1171_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref(v___x_1227_);
v_f_1181_ = v_a_1228_;
v___y_1182_ = v___y_1174_;
v___y_1183_ = v___y_1175_;
v___y_1184_ = v___y_1176_;
v___y_1185_ = v___y_1177_;
v___y_1186_ = v___y_1178_;
goto v___jp_1180_;
}
else
{
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v_x_1172_);
lean_dec_ref(v_post_1168_);
lean_dec_ref(v_pre_1167_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v_pre_1236_, lean_object* v_e_1237_, lean_object* v_post_1238_, uint8_t v_usedLetOnly_1239_, uint8_t v_skipConstInApp_1240_, uint8_t v_skipInstances_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
lean_inc_ref(v_pre_1236_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc_ref(v_e_1237_);
v___x_1248_ = lean_apply_6(v_pre_1236_, v_e_1237_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1297_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1297_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1297_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___y_1254_; 
switch(lean_obj_tag(v_a_1249_))
{
case 0:
{
lean_object* v_e_1289_; lean_object* v___x_1291_; 
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v_post_1238_);
lean_dec_ref(v_e_1237_);
lean_dec_ref(v_pre_1236_);
v_e_1289_ = lean_ctor_get(v_a_1249_, 0);
lean_inc_ref(v_e_1289_);
lean_dec_ref(v_a_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_e_1289_);
v___x_1291_ = v___x_1251_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_e_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
case 1:
{
lean_object* v_e_1293_; lean_object* v___x_1294_; 
lean_del_object(v___x_1251_);
lean_dec_ref(v_e_1237_);
v_e_1293_ = lean_ctor_get(v_a_1249_, 0);
lean_inc_ref(v_e_1293_);
lean_dec_ref(v_a_1249_);
v___x_1294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v_e_1293_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1294_;
}
default: 
{
lean_object* v_e_x3f_1295_; 
lean_del_object(v___x_1251_);
v_e_x3f_1295_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_e_x3f_1295_);
lean_dec_ref(v_a_1249_);
if (lean_obj_tag(v_e_x3f_1295_) == 0)
{
v___y_1254_ = v_e_1237_;
goto v___jp_1253_;
}
else
{
lean_object* v_val_1296_; 
lean_dec_ref(v_e_1237_);
v_val_1296_ = lean_ctor_get(v_e_x3f_1295_, 0);
lean_inc(v_val_1296_);
lean_dec_ref(v_e_x3f_1295_);
v___y_1254_ = v_val_1296_;
goto v___jp_1253_;
}
}
}
v___jp_1253_:
{
switch(lean_obj_tag(v___y_1254_))
{
case 7:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___x_1255_, v___y_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1256_;
}
case 6:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___x_1257_, v___y_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1258_;
}
case 8:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___x_1259_, v___y_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1260_;
}
case 5:
{
lean_object* v_dummy_1261_; lean_object* v_nargs_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_dummy_1261_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1262_ = l_Lean_Expr_getAppNumArgs(v___y_1254_);
lean_inc(v_nargs_1262_);
v___x_1263_ = lean_mk_array(v_nargs_1262_, v_dummy_1261_);
v___x_1264_ = lean_unsigned_to_nat(1u);
v___x_1265_ = lean_nat_sub(v_nargs_1262_, v___x_1264_);
lean_dec(v_nargs_1262_);
v___x_1266_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1241_, v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v___y_1254_, v___x_1263_, v___x_1265_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1266_;
}
case 10:
{
lean_object* v_data_1267_; lean_object* v_expr_1268_; lean_object* v___x_1269_; 
v_data_1267_ = lean_ctor_get(v___y_1254_, 0);
v_expr_1268_ = lean_ctor_get(v___y_1254_, 1);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v_expr_1268_);
lean_inc_ref(v_post_1238_);
lean_inc_ref(v_pre_1236_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v_expr_1268_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; size_t v___x_1271_; size_t v___x_1272_; uint8_t v___x_1273_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = lean_ptr_addr(v_expr_1268_);
v___x_1272_ = lean_ptr_addr(v_a_1270_);
v___x_1273_ = lean_usize_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc(v_data_1267_);
lean_dec_ref(v___y_1254_);
v___x_1274_ = l_Lean_Expr_mdata___override(v_data_1267_, v_a_1270_);
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___x_1274_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; 
lean_dec(v_a_1270_);
v___x_1276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___y_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1276_;
}
}
else
{
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v_post_1238_);
lean_dec_ref(v_pre_1236_);
return v___x_1269_;
}
}
case 11:
{
lean_object* v_typeName_1277_; lean_object* v_idx_1278_; lean_object* v_struct_1279_; lean_object* v___x_1280_; 
v_typeName_1277_ = lean_ctor_get(v___y_1254_, 0);
v_idx_1278_ = lean_ctor_get(v___y_1254_, 1);
v_struct_1279_ = lean_ctor_get(v___y_1254_, 2);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v_struct_1279_);
lean_inc_ref(v_post_1238_);
lean_inc_ref(v_pre_1236_);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v_struct_1279_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; size_t v___x_1282_; size_t v___x_1283_; uint8_t v___x_1284_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = lean_ptr_addr(v_struct_1279_);
v___x_1283_ = lean_ptr_addr(v_a_1281_);
v___x_1284_ = lean_usize_dec_eq(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_inc(v_idx_1278_);
lean_inc(v_typeName_1277_);
lean_dec_ref(v___y_1254_);
v___x_1285_ = l_Lean_Expr_proj___override(v_typeName_1277_, v_idx_1278_, v_a_1281_);
v___x_1286_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___x_1285_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; 
lean_dec(v_a_1281_);
v___x_1287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___y_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1287_;
}
}
else
{
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v_post_1238_);
lean_dec_ref(v_pre_1236_);
return v___x_1280_;
}
}
default: 
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1236_, v_post_1238_, v_usedLetOnly_1239_, v_skipConstInApp_1240_, v_skipInstances_1241_, v___y_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v_post_1238_);
lean_dec_ref(v_e_1237_);
lean_dec_ref(v_pre_1236_);
v_a_1298_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1248_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1248_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v_pre_1306_, lean_object* v_e_1307_, lean_object* v_post_1308_, lean_object* v_usedLetOnly_1309_, lean_object* v_skipConstInApp_1310_, lean_object* v_skipInstances_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_usedLetOnly_boxed_1318_; uint8_t v_skipConstInApp_boxed_1319_; uint8_t v_skipInstances_boxed_1320_; lean_object* v_res_1321_; 
v_usedLetOnly_boxed_1318_ = lean_unbox(v_usedLetOnly_1309_);
v_skipConstInApp_boxed_1319_ = lean_unbox(v_skipConstInApp_1310_);
v_skipInstances_boxed_1320_ = lean_unbox(v_skipInstances_1311_);
v_res_1321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v_pre_1306_, v_e_1307_, v_post_1308_, v_usedLetOnly_boxed_1318_, v_skipConstInApp_boxed_1319_, v_skipInstances_boxed_1320_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1322_, lean_object* v_post_1323_, uint8_t v_usedLetOnly_1324_, uint8_t v_skipConstInApp_1325_, uint8_t v_skipInstances_1326_, lean_object* v_e_1327_, lean_object* v_a_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_inc(v_a_1328_);
v___x_1334_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1334_, 0, lean_box(0));
lean_closure_set(v___x_1334_, 1, lean_box(0));
lean_closure_set(v___x_1334_, 2, v_a_1328_);
v___x_1335_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1334_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1369_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1369_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1369_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1336_, v_e_1327_);
lean_dec(v_a_1336_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; 
lean_del_object(v___x_1338_);
v___x_1341_ = lean_box(v_usedLetOnly_1324_);
v___x_1342_ = lean_box(v_skipConstInApp_1325_);
v___x_1343_ = lean_box(v_skipInstances_1326_);
lean_inc_ref(v_e_1327_);
v___f_1344_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1344_, 0, v_pre_1322_);
lean_closure_set(v___f_1344_, 1, v_e_1327_);
lean_closure_set(v___f_1344_, 2, v_post_1323_);
lean_closure_set(v___f_1344_, 3, v___x_1341_);
lean_closure_set(v___f_1344_, 4, v___x_1342_);
lean_closure_set(v___f_1344_, 5, v___x_1343_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v_a_1328_);
v___x_1345_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1344_, v_a_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
lean_inc(v_a_1346_);
v___f_1347_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1347_, 0, v_a_1328_);
lean_closure_set(v___f_1347_, 1, v_e_1327_);
lean_closure_set(v___f_1347_, 2, v_a_1346_);
v___x_1348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1347_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v___x_1348_, 0);
lean_dec(v_unused_1356_);
v___x_1350_ = v___x_1348_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_dec(v___x_1348_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_a_1346_);
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1346_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_a_1346_);
v_a_1357_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1348_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1348_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_e_1327_);
return v___x_1345_;
}
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1367_; 
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_e_1327_);
lean_dec_ref(v_post_1323_);
lean_dec_ref(v_pre_1322_);
v_val_1365_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_val_1365_);
lean_dec_ref(v___x_1340_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_val_1365_);
v___x_1367_ = v___x_1338_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_val_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_e_1327_);
lean_dec_ref(v_post_1323_);
lean_dec_ref(v_pre_1322_);
v_a_1370_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1335_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1335_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1378_, lean_object* v_pre_1379_, lean_object* v_post_1380_, lean_object* v_usedLetOnly_1381_, lean_object* v_skipConstInApp_1382_, lean_object* v_skipInstances_1383_, lean_object* v_body_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_usedLetOnly_boxed_1392_; uint8_t v_skipConstInApp_boxed_1393_; uint8_t v_skipInstances_boxed_1394_; lean_object* v_res_1395_; 
v_usedLetOnly_boxed_1392_ = lean_unbox(v_usedLetOnly_1381_);
v_skipConstInApp_boxed_1393_ = lean_unbox(v_skipConstInApp_1382_);
v_skipInstances_boxed_1394_ = lean_unbox(v_skipInstances_1383_);
v_res_1395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1378_, v_pre_1379_, v_post_1380_, v_usedLetOnly_boxed_1392_, v_skipConstInApp_boxed_1393_, v_skipInstances_boxed_1394_, v_body_1384_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1396_, lean_object* v_post_1397_, uint8_t v_usedLetOnly_1398_, uint8_t v_skipConstInApp_1399_, uint8_t v_skipInstances_1400_, lean_object* v_fvars_1401_, lean_object* v_e_1402_, lean_object* v_a_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
if (lean_obj_tag(v_e_1402_) == 7)
{
lean_object* v_binderName_1409_; lean_object* v_binderType_1410_; lean_object* v_body_1411_; uint8_t v_binderInfo_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_binderName_1409_ = lean_ctor_get(v_e_1402_, 0);
lean_inc(v_binderName_1409_);
v_binderType_1410_ = lean_ctor_get(v_e_1402_, 1);
lean_inc_ref(v_binderType_1410_);
v_body_1411_ = lean_ctor_get(v_e_1402_, 2);
lean_inc_ref(v_body_1411_);
v_binderInfo_1412_ = lean_ctor_get_uint8(v_e_1402_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1402_);
v___x_1413_ = lean_expr_instantiate_rev(v_binderType_1410_, v_fvars_1401_);
lean_dec_ref(v_binderType_1410_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v_a_1403_);
lean_inc_ref(v_post_1397_);
lean_inc_ref(v_pre_1396_);
v___x_1414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1396_, v_post_1397_, v_usedLetOnly_1398_, v_skipConstInApp_1399_, v_skipInstances_1400_, v___x_1413_, v_a_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___f_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref(v___x_1414_);
v___x_1416_ = lean_box(v_usedLetOnly_1398_);
v___x_1417_ = lean_box(v_skipConstInApp_1399_);
v___x_1418_ = lean_box(v_skipInstances_1400_);
v___f_1419_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1419_, 0, v_fvars_1401_);
lean_closure_set(v___f_1419_, 1, v_pre_1396_);
lean_closure_set(v___f_1419_, 2, v_post_1397_);
lean_closure_set(v___f_1419_, 3, v___x_1416_);
lean_closure_set(v___f_1419_, 4, v___x_1417_);
lean_closure_set(v___f_1419_, 5, v___x_1418_);
lean_closure_set(v___f_1419_, 6, v_body_1411_);
v___x_1420_ = 0;
v___x_1421_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1409_, v_binderInfo_1412_, v_a_1415_, v___f_1419_, v___x_1420_, v_a_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1421_;
}
else
{
lean_dec_ref(v_body_1411_);
lean_dec(v_binderName_1409_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_fvars_1401_);
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_expr_instantiate_rev(v_e_1402_, v_fvars_1401_);
lean_dec_ref(v_e_1402_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v_a_1403_);
lean_inc_ref(v_post_1397_);
lean_inc_ref(v_pre_1396_);
v___x_1423_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1396_, v_post_1397_, v_usedLetOnly_1398_, v_skipConstInApp_1399_, v_skipInstances_1400_, v___x_1422_, v_a_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = 0;
v___x_1426_ = 1;
v___x_1427_ = 1;
v___x_1428_ = l_Lean_Meta_mkForallFVars(v_fvars_1401_, v_a_1424_, v___x_1425_, v_usedLetOnly_1398_, v___x_1426_, v___x_1427_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec_ref(v_fvars_1401_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1396_, v_post_1397_, v_usedLetOnly_1398_, v_skipConstInApp_1399_, v_skipInstances_1400_, v_a_1429_, v_a_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1430_;
}
else
{
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
return v___x_1428_;
}
}
else
{
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_fvars_1401_);
lean_dec_ref(v_post_1397_);
lean_dec_ref(v_pre_1396_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1431_, lean_object* v_pre_1432_, lean_object* v_post_1433_, uint8_t v_usedLetOnly_1434_, uint8_t v_skipConstInApp_1435_, uint8_t v_skipInstances_1436_, lean_object* v_body_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_array_push(v_fvars_1431_, v_x_1438_);
v___x_1446_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1432_, v_post_1433_, v_usedLetOnly_1434_, v_skipConstInApp_1435_, v_skipInstances_1436_, v___x_1445_, v_body_1437_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1447_, lean_object* v_post_1448_, lean_object* v_usedLetOnly_1449_, lean_object* v_skipConstInApp_1450_, lean_object* v_skipInstances_1451_, lean_object* v_e_1452_, lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v_usedLetOnly_boxed_1459_; uint8_t v_skipConstInApp_boxed_1460_; uint8_t v_skipInstances_boxed_1461_; lean_object* v_res_1462_; 
v_usedLetOnly_boxed_1459_ = lean_unbox(v_usedLetOnly_1449_);
v_skipConstInApp_boxed_1460_ = lean_unbox(v_skipConstInApp_1450_);
v_skipInstances_boxed_1461_ = lean_unbox(v_skipInstances_1451_);
v_res_1462_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1447_, v_post_1448_, v_usedLetOnly_boxed_1459_, v_skipConstInApp_boxed_1460_, v_skipInstances_boxed_1461_, v_e_1452_, v_a_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1463_, lean_object* v_post_1464_, lean_object* v_usedLetOnly_1465_, lean_object* v_skipConstInApp_1466_, lean_object* v_skipInstances_1467_, lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_bs_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v_usedLetOnly_boxed_1477_; uint8_t v_skipConstInApp_boxed_1478_; uint8_t v_skipInstances_boxed_1479_; size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_usedLetOnly_boxed_1477_ = lean_unbox(v_usedLetOnly_1465_);
v_skipConstInApp_boxed_1478_ = lean_unbox(v_skipConstInApp_1466_);
v_skipInstances_boxed_1479_ = lean_unbox(v_skipInstances_1467_);
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1463_, v_post_1464_, v_usedLetOnly_boxed_1477_, v_skipConstInApp_boxed_1478_, v_skipInstances_boxed_1479_, v_sz_boxed_1480_, v_i_boxed_1481_, v_bs_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1483_, lean_object* v_post_1484_, lean_object* v_usedLetOnly_1485_, lean_object* v_skipConstInApp_1486_, lean_object* v_skipInstances_1487_, lean_object* v_e_1488_, lean_object* v_a_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_usedLetOnly_boxed_1495_; uint8_t v_skipConstInApp_boxed_1496_; uint8_t v_skipInstances_boxed_1497_; lean_object* v_res_1498_; 
v_usedLetOnly_boxed_1495_ = lean_unbox(v_usedLetOnly_1485_);
v_skipConstInApp_boxed_1496_ = lean_unbox(v_skipConstInApp_1486_);
v_skipInstances_boxed_1497_ = lean_unbox(v_skipInstances_1487_);
v_res_1498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1483_, v_post_1484_, v_usedLetOnly_boxed_1495_, v_skipConstInApp_boxed_1496_, v_skipInstances_boxed_1497_, v_e_1488_, v_a_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1499_, lean_object* v_post_1500_, lean_object* v_usedLetOnly_1501_, lean_object* v_skipConstInApp_1502_, lean_object* v_skipInstances_1503_, lean_object* v_fvars_1504_, lean_object* v_e_1505_, lean_object* v_a_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v_usedLetOnly_boxed_1512_; uint8_t v_skipConstInApp_boxed_1513_; uint8_t v_skipInstances_boxed_1514_; lean_object* v_res_1515_; 
v_usedLetOnly_boxed_1512_ = lean_unbox(v_usedLetOnly_1501_);
v_skipConstInApp_boxed_1513_ = lean_unbox(v_skipConstInApp_1502_);
v_skipInstances_boxed_1514_ = lean_unbox(v_skipInstances_1503_);
v_res_1515_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1499_, v_post_1500_, v_usedLetOnly_boxed_1512_, v_skipConstInApp_boxed_1513_, v_skipInstances_boxed_1514_, v_fvars_1504_, v_e_1505_, v_a_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1516_, lean_object* v_post_1517_, lean_object* v_usedLetOnly_1518_, lean_object* v_skipConstInApp_1519_, lean_object* v_skipInstances_1520_, lean_object* v_fvars_1521_, lean_object* v_e_1522_, lean_object* v_a_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v_usedLetOnly_boxed_1529_; uint8_t v_skipConstInApp_boxed_1530_; uint8_t v_skipInstances_boxed_1531_; lean_object* v_res_1532_; 
v_usedLetOnly_boxed_1529_ = lean_unbox(v_usedLetOnly_1518_);
v_skipConstInApp_boxed_1530_ = lean_unbox(v_skipConstInApp_1519_);
v_skipInstances_boxed_1531_ = lean_unbox(v_skipInstances_1520_);
v_res_1532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1516_, v_post_1517_, v_usedLetOnly_boxed_1529_, v_skipConstInApp_boxed_1530_, v_skipInstances_boxed_1531_, v_fvars_1521_, v_e_1522_, v_a_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1533_, lean_object* v_post_1534_, lean_object* v_usedLetOnly_1535_, lean_object* v_skipConstInApp_1536_, lean_object* v_skipInstances_1537_, lean_object* v_fvars_1538_, lean_object* v_e_1539_, lean_object* v_a_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
uint8_t v_usedLetOnly_boxed_1546_; uint8_t v_skipConstInApp_boxed_1547_; uint8_t v_skipInstances_boxed_1548_; lean_object* v_res_1549_; 
v_usedLetOnly_boxed_1546_ = lean_unbox(v_usedLetOnly_1535_);
v_skipConstInApp_boxed_1547_ = lean_unbox(v_skipConstInApp_1536_);
v_skipInstances_boxed_1548_ = lean_unbox(v_skipInstances_1537_);
v_res_1549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1533_, v_post_1534_, v_usedLetOnly_boxed_1546_, v_skipConstInApp_boxed_1547_, v_skipInstances_boxed_1548_, v_fvars_1538_, v_e_1539_, v_a_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1550_, lean_object* v___x_1551_, lean_object* v_pre_1552_, lean_object* v_post_1553_, lean_object* v_usedLetOnly_1554_, lean_object* v_skipConstInApp_1555_, lean_object* v_skipInstances_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v_usedLetOnly_boxed_1565_; uint8_t v_skipConstInApp_boxed_1566_; uint8_t v_skipInstances_boxed_1567_; lean_object* v_res_1568_; 
v_usedLetOnly_boxed_1565_ = lean_unbox(v_usedLetOnly_1554_);
v_skipConstInApp_boxed_1566_ = lean_unbox(v_skipConstInApp_1555_);
v_skipInstances_boxed_1567_ = lean_unbox(v_skipInstances_1556_);
v_res_1568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1550_, v___x_1551_, v_pre_1552_, v_post_1553_, v_usedLetOnly_boxed_1565_, v_skipConstInApp_boxed_1566_, v_skipInstances_boxed_1567_, v_a_1557_, v_b_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec_ref(v___x_1551_);
lean_dec(v_upperBound_1550_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1569_, lean_object* v_pre_1570_, lean_object* v_post_1571_, lean_object* v_usedLetOnly_1572_, lean_object* v_skipConstInApp_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v_skipInstances_boxed_1583_; uint8_t v_usedLetOnly_boxed_1584_; uint8_t v_skipConstInApp_boxed_1585_; lean_object* v_res_1586_; 
v_skipInstances_boxed_1583_ = lean_unbox(v_skipInstances_1569_);
v_usedLetOnly_boxed_1584_ = lean_unbox(v_usedLetOnly_1572_);
v_skipConstInApp_boxed_1585_ = lean_unbox(v_skipConstInApp_1573_);
v_res_1586_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1583_, v_pre_1570_, v_post_1571_, v_usedLetOnly_boxed_1584_, v_skipConstInApp_boxed_1585_, v_x_1574_, v_x_1575_, v_x_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
return v_res_1586_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_unsigned_to_nat(16u);
v___x_1589_ = lean_mk_array(v___x_1588_, v___x_1587_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
lean_ctor_set(v___x_1592_, 1, v___x_1590_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1594_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1594_, 0, lean_box(0));
lean_closure_set(v___x_1594_, 1, lean_box(0));
lean_closure_set(v___x_1594_, 2, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1595_, lean_object* v_pre_1596_, lean_object* v_post_1597_, uint8_t v_usedLetOnly_1598_, uint8_t v_skipConstInApp_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v_a_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1605_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1606_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1605_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = 0;
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
lean_inc(v_a_1607_);
v___x_1609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1596_, v_post_1597_, v_usedLetOnly_1598_, v_skipConstInApp_1599_, v___x_1608_, v_input_1595_, v_a_1607_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1611_, 0, lean_box(0));
lean_closure_set(v___x_1611_, 1, lean_box(0));
lean_closure_set(v___x_1611_, 2, v_a_1607_);
v___x_1612_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1611_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; 
v_unused_1620_ = lean_ctor_get(v___x_1612_, 0);
lean_dec(v_unused_1620_);
v___x_1614_ = v___x_1612_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_dec(v___x_1612_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v_a_1610_);
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1610_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_dec(v_a_1607_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1621_, lean_object* v_pre_1622_, lean_object* v_post_1623_, lean_object* v_usedLetOnly_1624_, lean_object* v_skipConstInApp_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
uint8_t v_usedLetOnly_boxed_1631_; uint8_t v_skipConstInApp_boxed_1632_; lean_object* v_res_1633_; 
v_usedLetOnly_boxed_1631_ = lean_unbox(v_usedLetOnly_1624_);
v_skipConstInApp_boxed_1632_ = lean_unbox(v_skipConstInApp_1625_);
v_res_1633_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1621_, v_pre_1622_, v_post_1623_, v_usedLetOnly_boxed_1631_, v_skipConstInApp_boxed_1632_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v_res_1633_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__2(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__1));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__4(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__3));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1641_, lean_object* v_argsPacker_1642_, lean_object* v_funNames_1643_, lean_object* v_newF_1644_, lean_object* v_e_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v___x_1651_; 
lean_inc(v_a_1649_);
lean_inc_ref(v_a_1648_);
lean_inc(v_a_1647_);
lean_inc_ref(v_a_1646_);
lean_inc_ref(v_newF_1644_);
v___x_1651_ = lean_infer_type(v_newF_1644_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___f_1653_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; uint8_t v___x_1664_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref(v___x_1651_);
v___f_1653_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1664_ = l_Lean_Expr_isForall(v_a_1652_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_e_1645_);
lean_dec_ref(v_funNames_1643_);
lean_dec_ref(v_argsPacker_1642_);
lean_dec_ref(v_fixedParamPerms_1641_);
v___x_1665_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__2, &l_Lean_Elab_WF_packCalls___closed__2_once, _init_l_Lean_Elab_WF_packCalls___closed__2);
v___x_1666_ = l_Lean_MessageData_ofExpr(v_newF_1644_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__4, &l_Lean_Elab_WF_packCalls___closed__4_once, _init_l_Lean_Elab_WF_packCalls___closed__4);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_MessageData_ofExpr(v_a_1652_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1671_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
v___y_1655_ = v_a_1646_;
v___y_1656_ = v_a_1647_;
v___y_1657_ = v_a_1648_;
v___y_1658_ = v_a_1649_;
goto v___jp_1654_;
}
v___jp_1654_:
{
lean_object* v___x_1659_; lean_object* v___f_1660_; uint8_t v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1659_ = l_Lean_Expr_bindingDomain_x21(v_a_1652_);
lean_dec(v_a_1652_);
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1660_, 0, v_funNames_1643_);
lean_closure_set(v___f_1660_, 1, v_fixedParamPerms_1641_);
lean_closure_set(v___f_1660_, 2, v_argsPacker_1642_);
lean_closure_set(v___f_1660_, 3, v___x_1659_);
lean_closure_set(v___f_1660_, 4, v_newF_1644_);
v___x_1661_ = 0;
v___x_1662_ = 1;
v___x_1663_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1645_, v___f_1653_, v___f_1660_, v___x_1661_, v___x_1662_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
return v___x_1663_;
}
}
else
{
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec_ref(v_e_1645_);
lean_dec_ref(v_newF_1644_);
lean_dec_ref(v_funNames_1643_);
lean_dec_ref(v_argsPacker_1642_);
lean_dec_ref(v_fixedParamPerms_1641_);
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1681_, lean_object* v_argsPacker_1682_, lean_object* v_funNames_1683_, lean_object* v_newF_1684_, lean_object* v_e_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1681_, v_argsPacker_1682_, v_funNames_1683_, v_newF_1684_, v_e_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1692_, lean_object* v___x_1693_, lean_object* v_pre_1694_, lean_object* v_post_1695_, uint8_t v_usedLetOnly_1696_, uint8_t v_skipConstInApp_1697_, uint8_t v_skipInstances_1698_, lean_object* v___x_1699_, lean_object* v_inst_1700_, lean_object* v_R_1701_, lean_object* v_a_1702_, lean_object* v_b_1703_, lean_object* v_c_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1692_, v___x_1693_, v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v_a_1702_, v_b_1703_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1712_ = _args[0];
lean_object* v___x_1713_ = _args[1];
lean_object* v_pre_1714_ = _args[2];
lean_object* v_post_1715_ = _args[3];
lean_object* v_usedLetOnly_1716_ = _args[4];
lean_object* v_skipConstInApp_1717_ = _args[5];
lean_object* v_skipInstances_1718_ = _args[6];
lean_object* v___x_1719_ = _args[7];
lean_object* v_inst_1720_ = _args[8];
lean_object* v_R_1721_ = _args[9];
lean_object* v_a_1722_ = _args[10];
lean_object* v_b_1723_ = _args[11];
lean_object* v_c_1724_ = _args[12];
lean_object* v___y_1725_ = _args[13];
lean_object* v___y_1726_ = _args[14];
lean_object* v___y_1727_ = _args[15];
lean_object* v___y_1728_ = _args[16];
lean_object* v___y_1729_ = _args[17];
lean_object* v___y_1730_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1731_; uint8_t v_skipConstInApp_boxed_1732_; uint8_t v_skipInstances_boxed_1733_; lean_object* v_res_1734_; 
v_usedLetOnly_boxed_1731_ = lean_unbox(v_usedLetOnly_1716_);
v_skipConstInApp_boxed_1732_ = lean_unbox(v_skipConstInApp_1717_);
v_skipInstances_boxed_1733_ = lean_unbox(v_skipInstances_1718_);
v_res_1734_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1712_, v___x_1713_, v_pre_1714_, v_post_1715_, v_usedLetOnly_boxed_1731_, v_skipConstInApp_boxed_1732_, v_skipInstances_boxed_1733_, v___x_1719_, v_inst_1720_, v_R_1721_, v_a_1722_, v_b_1723_, v_c_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___x_1719_);
lean_dec_ref(v___x_1713_);
lean_dec(v_upperBound_1712_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1735_, lean_object* v_m_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1736_, v_a_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1739_, lean_object* v_m_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1739_, v_m_1740_, v_a_1741_);
lean_dec_ref(v_a_1741_);
lean_dec_ref(v_m_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1743_, lean_object* v_name_1744_, uint8_t v_bi_1745_, lean_object* v_type_1746_, lean_object* v_k_1747_, uint8_t v_kind_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1744_, v_bi_1745_, v_type_1746_, v_k_1747_, v_kind_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_name_1757_, lean_object* v_bi_1758_, lean_object* v_type_1759_, lean_object* v_k_1760_, lean_object* v_kind_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v_bi_boxed_1768_; uint8_t v_kind_boxed_1769_; lean_object* v_res_1770_; 
v_bi_boxed_1768_ = lean_unbox(v_bi_1758_);
v_kind_boxed_1769_ = lean_unbox(v_kind_1761_);
v_res_1770_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1756_, v_name_1757_, v_bi_boxed_1768_, v_type_1759_, v_k_1760_, v_kind_boxed_1769_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1771_, lean_object* v_name_1772_, lean_object* v_type_1773_, lean_object* v_val_1774_, lean_object* v_k_1775_, uint8_t v_nondep_1776_, uint8_t v_kind_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1772_, v_type_1773_, v_val_1774_, v_k_1775_, v_nondep_1776_, v_kind_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_name_1786_, lean_object* v_type_1787_, lean_object* v_val_1788_, lean_object* v_k_1789_, lean_object* v_nondep_1790_, lean_object* v_kind_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint8_t v_nondep_boxed_1798_; uint8_t v_kind_boxed_1799_; lean_object* v_res_1800_; 
v_nondep_boxed_1798_ = lean_unbox(v_nondep_1790_);
v_kind_boxed_1799_ = lean_unbox(v_kind_1791_);
v_res_1800_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1785_, v_name_1786_, v_type_1787_, v_val_1788_, v_k_1789_, v_nondep_boxed_1798_, v_kind_boxed_1799_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1801_, lean_object* v_ref_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1802_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_ref_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1809_, v_ref_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1826_, v_x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1835_, lean_object* v_m_1836_, lean_object* v_a_1837_, lean_object* v_b_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1836_, v_a_1837_, v_b_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1840_, lean_object* v_a_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1844_, lean_object* v_a_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1844_, v_a_1845_, v_x_1846_);
lean_dec(v_x_1846_);
lean_dec_ref(v_a_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1848_, lean_object* v_a_1849_, lean_object* v_x_1850_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1852_, lean_object* v_a_1853_, lean_object* v_x_1854_){
_start:
{
uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_res_1855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1852_, v_a_1853_, v_x_1854_);
lean_dec(v_x_1854_);
lean_dec_ref(v_a_1853_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1857_, lean_object* v_data_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1860_, lean_object* v_a_1861_, lean_object* v_b_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1861_, v_b_1862_, v_x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1865_, lean_object* v_i_1866_, lean_object* v_source_1867_, lean_object* v_target_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1866_, v_source_1867_, v_target_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1871_, v_x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1880_, lean_object* v_argsPacker_1881_, lean_object* v_preDefs_1882_){
_start:
{
uint8_t v___y_1884_; uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1880_);
if (v___x_1904_ == 0)
{
v___y_1884_ = v___x_1904_;
goto v___jp_1883_;
}
else
{
uint8_t v___x_1905_; 
v___x_1905_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1881_);
v___y_1884_ = v___x_1905_;
goto v___jp_1883_;
}
v___jp_1883_:
{
if (v___y_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1881_);
v___x_1887_ = lean_nat_dec_lt(v___x_1885_, v___x_1886_);
lean_dec(v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_declName_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1888_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_array_get_borrowed(v___x_1888_, v_preDefs_1882_, v___x_1889_);
v_declName_1891_ = lean_ctor_get(v___x_1890_, 3);
v___x_1892_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1891_);
v___x_1893_ = l_Lean_Name_append(v_declName_1891_, v___x_1892_);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_declName_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1894_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_array_get_borrowed(v___x_1894_, v_preDefs_1882_, v___x_1895_);
v_declName_1897_ = lean_ctor_get(v___x_1896_, 3);
v___x_1898_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1897_);
v___x_1899_ = l_Lean_Name_append(v_declName_1897_, v___x_1898_);
return v___x_1899_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_declName_1903_; 
v___x_1900_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_array_get_borrowed(v___x_1900_, v_preDefs_1882_, v___x_1901_);
v_declName_1903_ = lean_ctor_get(v___x_1902_, 3);
lean_inc(v_declName_1903_);
return v_declName_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1906_, lean_object* v_argsPacker_1907_, lean_object* v_preDefs_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1906_, v_argsPacker_1907_, v_preDefs_1908_);
lean_dec_ref(v_preDefs_1908_);
lean_dec_ref(v_argsPacker_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1910_, lean_object* v_b_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_apply_6(v_k_1910_, v_b_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, lean_box(0));
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1918_, lean_object* v_b_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1918_, v_b_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1926_, lean_object* v_type_1927_, lean_object* v_k_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___f_1934_; lean_object* v___x_1935_; 
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1934_, 0, v_k_1928_);
v___x_1935_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1926_, v_type_1927_, v___f_1934_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1935_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1952_, lean_object* v_type_1953_, lean_object* v_k_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1952_, v_type_1953_, v_k_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1961_, lean_object* v_perm_1962_, lean_object* v_type_1963_, lean_object* v_k_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1962_, v_type_1963_, v_k_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1971_, lean_object* v_perm_1972_, lean_object* v_type_1973_, lean_object* v_k_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1971_, v_perm_1972_, v_type_1973_, v_k_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1981_, lean_object* v_ys_1982_, lean_object* v_as_1983_, lean_object* v_i_1984_, lean_object* v_j_1985_, lean_object* v_bs_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_zero_1992_; uint8_t v_isZero_1993_; 
v_zero_1992_ = lean_unsigned_to_nat(0u);
v_isZero_1993_ = lean_nat_dec_eq(v_i_1984_, v_zero_1992_);
if (v_isZero_1993_ == 1)
{
lean_object* v___x_1994_; 
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v_j_1985_);
lean_dec(v_i_1984_);
lean_dec_ref(v_ys_1982_);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_bs_1986_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; lean_object* v_value_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1995_ = lean_array_fget_borrowed(v_as_1983_, v_j_1985_);
v_value_1996_ = lean_ctor_get(v___x_1995_, 7);
v___x_1997_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_1998_ = lean_array_get_borrowed(v___x_1997_, v___x_1981_, v_j_1985_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc_ref(v_ys_1982_);
lean_inc_ref(v_value_1996_);
lean_inc(v___x_1998_);
v___x_1999_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1998_, v_value_1996_, v_ys_1982_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_one_2001_; lean_object* v_n_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1999_);
v_one_2001_ = lean_unsigned_to_nat(1u);
v_n_2002_ = lean_nat_sub(v_i_1984_, v_one_2001_);
lean_dec(v_i_1984_);
v___x_2003_ = lean_nat_add(v_j_1985_, v_one_2001_);
lean_dec(v_j_1985_);
v___x_2004_ = lean_array_push(v_bs_1986_, v_a_2000_);
v_i_1984_ = v_n_2002_;
v_j_1985_ = v___x_2003_;
v_bs_1986_ = v___x_2004_;
goto _start;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v_bs_1986_);
lean_dec(v_j_1985_);
lean_dec(v_i_1984_);
lean_dec_ref(v_ys_1982_);
v_a_2006_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1999_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1999_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2014_, lean_object* v_ys_2015_, lean_object* v_as_2016_, lean_object* v_i_2017_, lean_object* v_j_2018_, lean_object* v_bs_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2014_, v_ys_2015_, v_as_2016_, v_i_2017_, v_j_2018_, v_bs_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec_ref(v_as_2016_);
lean_dec_ref(v___x_2014_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2026_, lean_object* v_ys_2027_, lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_j_2030_, lean_object* v_bs_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_zero_2037_; uint8_t v_isZero_2038_; 
v_zero_2037_ = lean_unsigned_to_nat(0u);
v_isZero_2038_ = lean_nat_dec_eq(v_i_2029_, v_zero_2037_);
if (v_isZero_2038_ == 1)
{
lean_object* v___x_2039_; 
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v_j_2030_);
lean_dec(v_i_2029_);
lean_dec_ref(v_ys_2027_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_bs_2031_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v_type_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2040_ = lean_array_fget_borrowed(v_as_2028_, v_j_2030_);
v_type_2041_ = lean_ctor_get(v___x_2040_, 6);
v___x_2042_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2043_ = lean_array_get_borrowed(v___x_2042_, v___x_2026_, v_j_2030_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
lean_inc_ref(v_ys_2027_);
lean_inc_ref(v_type_2041_);
lean_inc(v___x_2043_);
v___x_2044_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2043_, v_type_2041_, v_ys_2027_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v_one_2046_; lean_object* v_n_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v_one_2046_ = lean_unsigned_to_nat(1u);
v_n_2047_ = lean_nat_sub(v_i_2029_, v_one_2046_);
lean_dec(v_i_2029_);
v___x_2048_ = lean_nat_add(v_j_2030_, v_one_2046_);
lean_dec(v_j_2030_);
v___x_2049_ = lean_array_push(v_bs_2031_, v_a_2045_);
v_i_2029_ = v_n_2047_;
v_j_2030_ = v___x_2048_;
v_bs_2031_ = v___x_2049_;
goto _start;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec_ref(v_bs_2031_);
lean_dec(v_j_2030_);
lean_dec(v_i_2029_);
lean_dec_ref(v_ys_2027_);
v_a_2051_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2044_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2044_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2059_, lean_object* v_ys_2060_, lean_object* v_as_2061_, lean_object* v_i_2062_, lean_object* v_j_2063_, lean_object* v_bs_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2059_, v_ys_2060_, v_as_2061_, v_i_2062_, v_j_2063_, v_bs_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v_as_2061_);
lean_dec_ref(v___x_2059_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
if (lean_obj_tag(v_a_2071_) == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = l_List_reverse___redArg(v_a_2072_);
return v___x_2073_;
}
else
{
lean_object* v_head_2074_; lean_object* v_tail_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2084_; 
v_head_2074_ = lean_ctor_get(v_a_2071_, 0);
v_tail_2075_ = lean_ctor_get(v_a_2071_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_a_2071_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2077_ = v_a_2071_;
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_tail_2075_);
lean_inc(v_head_2074_);
lean_dec(v_a_2071_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = l_Lean_mkLevelParam(v_head_2074_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_a_2072_);
lean_ctor_set(v___x_2077_, 0, v___x_2079_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_a_2072_);
v___x_2081_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
v_a_2071_ = v_tail_2075_;
v_a_2072_ = v___x_2081_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_bs_2087_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_usize_dec_lt(v_i_2086_, v_sz_2085_);
if (v___x_2088_ == 0)
{
return v_bs_2087_;
}
else
{
lean_object* v_v_2089_; lean_object* v_declName_2090_; lean_object* v___x_2091_; lean_object* v_bs_x27_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_v_2089_ = lean_array_uget_borrowed(v_bs_2087_, v_i_2086_);
v_declName_2090_ = lean_ctor_get(v_v_2089_, 3);
lean_inc(v_declName_2090_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v_bs_x27_2092_ = lean_array_uset(v_bs_2087_, v_i_2086_, v___x_2091_);
v___x_2093_ = ((size_t)1ULL);
v___x_2094_ = lean_usize_add(v_i_2086_, v___x_2093_);
v___x_2095_ = lean_array_uset(v_bs_x27_2092_, v_i_2086_, v_declName_2090_);
v_i_2086_ = v___x_2094_;
v_bs_2087_ = v___x_2095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2097_, lean_object* v_i_2098_, lean_object* v_bs_2099_){
_start:
{
size_t v_sz_boxed_2100_; size_t v_i_boxed_2101_; lean_object* v_res_2102_; 
v_sz_boxed_2100_ = lean_unbox_usize(v_sz_2097_);
lean_dec(v_sz_2097_);
v_i_boxed_2101_ = lean_unbox_usize(v_i_2098_);
lean_dec(v_i_2098_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2100_, v_i_boxed_2101_, v_bs_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2103_, lean_object* v_perms_2104_, lean_object* v___x_2105_, lean_object* v_argsPacker_2106_, uint8_t v___x_2107_, lean_object* v_ref_2108_, uint8_t v_kind_2109_, lean_object* v_levelParams_2110_, lean_object* v_modifiers_2111_, lean_object* v_newFn_2112_, lean_object* v_binders_2113_, lean_object* v_numSectionVars_2114_, lean_object* v_value_2115_, lean_object* v_termination_2116_, lean_object* v_fixedParamPerms_2117_, lean_object* v_ys_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_array_get_size(v_preDefs_2103_);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc_ref(v___x_2125_);
lean_inc(v___x_2105_);
lean_inc_ref(v_ys_2118_);
v___x_2126_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2104_, v_ys_2118_, v_preDefs_2103_, v___x_2124_, v___x_2105_, v___x_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc_ref(v_ys_2118_);
v___x_2128_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2104_, v_ys_2118_, v_preDefs_2103_, v___x_2124_, v___x_2105_, v___x_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref(v___x_2128_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
v___x_2130_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2106_, v_a_2127_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v_a_2127_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = 1;
v___x_2133_ = 1;
v___x_2134_ = l_Lean_Meta_mkForallFVars(v_ys_2118_, v_a_2131_, v___x_2107_, v___x_2132_, v___x_2132_, v___x_2133_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
lean_inc_ref(v_termination_2116_);
lean_inc(v_a_2135_);
lean_inc(v_numSectionVars_2114_);
lean_inc(v_binders_2113_);
lean_inc(v_newFn_2112_);
lean_inc_ref(v_modifiers_2111_);
lean_inc(v_levelParams_2110_);
lean_inc(v_ref_2108_);
v___x_2136_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2136_, 0, v_ref_2108_);
lean_ctor_set(v___x_2136_, 1, v_levelParams_2110_);
lean_ctor_set(v___x_2136_, 2, v_modifiers_2111_);
lean_ctor_set(v___x_2136_, 3, v_newFn_2112_);
lean_ctor_set(v___x_2136_, 4, v_binders_2113_);
lean_ctor_set(v___x_2136_, 5, v_numSectionVars_2114_);
lean_ctor_set(v___x_2136_, 6, v_a_2135_);
lean_ctor_set(v___x_2136_, 7, v_value_2115_);
lean_ctor_set(v___x_2136_, 8, v_termination_2116_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*9, v_kind_2109_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
v___x_2137_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2136_, v___y_2121_, v___y_2122_);
lean_dec_ref(v___x_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v___x_2137_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
v___x_2138_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2106_, v_a_2129_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v_a_2129_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; size_t v_sz_2144_; size_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = lean_box(0);
lean_inc(v_levelParams_2110_);
v___x_2141_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2110_, v___x_2140_);
lean_inc(v_newFn_2112_);
v___x_2142_ = l_Lean_mkConst(v_newFn_2112_, v___x_2141_);
v___x_2143_ = l_Lean_mkAppN(v___x_2142_, v_ys_2118_);
v_sz_2144_ = lean_array_size(v_preDefs_2103_);
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2144_, v___x_2145_, v_preDefs_2103_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
v___x_2147_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2117_, v_argsPacker_2106_, v___x_2146_, v___x_2143_, v_a_2139_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = l_Lean_Meta_mkLambdaFVars(v_ys_2118_, v_a_2148_, v___x_2107_, v___x_2132_, v___x_2107_, v___x_2132_, v___x_2133_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2154_, 0, v_ref_2108_);
lean_ctor_set(v___x_2154_, 1, v_levelParams_2110_);
lean_ctor_set(v___x_2154_, 2, v_modifiers_2111_);
lean_ctor_set(v___x_2154_, 3, v_newFn_2112_);
lean_ctor_set(v___x_2154_, 4, v_binders_2113_);
lean_ctor_set(v___x_2154_, 5, v_numSectionVars_2114_);
lean_ctor_set(v___x_2154_, 6, v_a_2135_);
lean_ctor_set(v___x_2154_, 7, v_a_2150_);
lean_ctor_set(v___x_2154_, 8, v_termination_2116_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*9, v_kind_2109_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2135_);
lean_dec_ref(v_termination_2116_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
v_a_2159_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2149_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2149_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_a_2135_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_termination_2116_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
v_a_2167_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2147_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2147_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2135_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_fixedParamPerms_2117_);
lean_dec_ref(v_termination_2116_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
lean_dec_ref(v_argsPacker_2106_);
lean_dec_ref(v_preDefs_2103_);
v_a_2175_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2138_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2138_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_a_2135_);
lean_dec(v_a_2129_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_fixedParamPerms_2117_);
lean_dec_ref(v_termination_2116_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
lean_dec_ref(v_argsPacker_2106_);
lean_dec_ref(v_preDefs_2103_);
v_a_2183_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2137_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2137_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_a_2129_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_fixedParamPerms_2117_);
lean_dec_ref(v_termination_2116_);
lean_dec_ref(v_value_2115_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
lean_dec_ref(v_argsPacker_2106_);
lean_dec_ref(v_preDefs_2103_);
v_a_2191_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2134_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2134_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_a_2129_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_fixedParamPerms_2117_);
lean_dec_ref(v_termination_2116_);
lean_dec_ref(v_value_2115_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
lean_dec_ref(v_argsPacker_2106_);
lean_dec_ref(v_preDefs_2103_);
v_a_2199_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2130_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2130_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2127_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_fixedParamPerms_2117_);
lean_dec_ref(v_termination_2116_);
lean_dec_ref(v_value_2115_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
lean_dec_ref(v_argsPacker_2106_);
lean_dec_ref(v_preDefs_2103_);
v_a_2207_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2128_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2128_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v___x_2125_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_ys_2118_);
lean_dec_ref(v_fixedParamPerms_2117_);
lean_dec_ref(v_termination_2116_);
lean_dec_ref(v_value_2115_);
lean_dec(v_numSectionVars_2114_);
lean_dec(v_binders_2113_);
lean_dec(v_newFn_2112_);
lean_dec_ref(v_modifiers_2111_);
lean_dec(v_levelParams_2110_);
lean_dec(v_ref_2108_);
lean_dec_ref(v_argsPacker_2106_);
lean_dec(v___x_2105_);
lean_dec_ref(v_preDefs_2103_);
v_a_2215_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2126_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2126_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2223_ = _args[0];
lean_object* v_perms_2224_ = _args[1];
lean_object* v___x_2225_ = _args[2];
lean_object* v_argsPacker_2226_ = _args[3];
lean_object* v___x_2227_ = _args[4];
lean_object* v_ref_2228_ = _args[5];
lean_object* v_kind_2229_ = _args[6];
lean_object* v_levelParams_2230_ = _args[7];
lean_object* v_modifiers_2231_ = _args[8];
lean_object* v_newFn_2232_ = _args[9];
lean_object* v_binders_2233_ = _args[10];
lean_object* v_numSectionVars_2234_ = _args[11];
lean_object* v_value_2235_ = _args[12];
lean_object* v_termination_2236_ = _args[13];
lean_object* v_fixedParamPerms_2237_ = _args[14];
lean_object* v_ys_2238_ = _args[15];
lean_object* v___y_2239_ = _args[16];
lean_object* v___y_2240_ = _args[17];
lean_object* v___y_2241_ = _args[18];
lean_object* v___y_2242_ = _args[19];
lean_object* v___y_2243_ = _args[20];
_start:
{
uint8_t v___x_2619__boxed_2244_; uint8_t v_kind_boxed_2245_; lean_object* v_res_2246_; 
v___x_2619__boxed_2244_ = lean_unbox(v___x_2227_);
v_kind_boxed_2245_ = lean_unbox(v_kind_2229_);
v_res_2246_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2223_, v_perms_2224_, v___x_2225_, v_argsPacker_2226_, v___x_2619__boxed_2244_, v_ref_2228_, v_kind_boxed_2245_, v_levelParams_2230_, v_modifiers_2231_, v_newFn_2232_, v_binders_2233_, v_numSectionVars_2234_, v_value_2235_, v_termination_2236_, v_fixedParamPerms_2237_, v_ys_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec_ref(v_perms_2224_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2247_, lean_object* v_argsPacker_2248_, lean_object* v_preDefs_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_ref_2258_; uint8_t v_kind_2259_; lean_object* v_levelParams_2260_; lean_object* v_modifiers_2261_; lean_object* v_declName_2262_; lean_object* v_binders_2263_; lean_object* v_numSectionVars_2264_; lean_object* v_type_2265_; lean_object* v_value_2266_; lean_object* v_termination_2267_; lean_object* v_newFn_2268_; uint8_t v___x_2269_; 
v___x_2255_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = lean_array_get_borrowed(v___x_2255_, v_preDefs_2249_, v___x_2256_);
v_ref_2258_ = lean_ctor_get(v___x_2257_, 0);
v_kind_2259_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*9);
v_levelParams_2260_ = lean_ctor_get(v___x_2257_, 1);
v_modifiers_2261_ = lean_ctor_get(v___x_2257_, 2);
v_declName_2262_ = lean_ctor_get(v___x_2257_, 3);
v_binders_2263_ = lean_ctor_get(v___x_2257_, 4);
v_numSectionVars_2264_ = lean_ctor_get(v___x_2257_, 5);
v_type_2265_ = lean_ctor_get(v___x_2257_, 6);
v_value_2266_ = lean_ctor_get(v___x_2257_, 7);
v_termination_2267_ = lean_ctor_get(v___x_2257_, 8);
lean_inc_ref(v_fixedParamPerms_2247_);
v_newFn_2268_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2247_, v_argsPacker_2248_, v_preDefs_2249_);
v___x_2269_ = lean_name_eq(v_newFn_2268_, v_declName_2262_);
if (v___x_2269_ == 0)
{
lean_object* v_perms_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_inc_ref(v_termination_2267_);
lean_inc_ref(v_value_2266_);
lean_inc_ref(v_type_2265_);
lean_inc(v_numSectionVars_2264_);
lean_inc(v_binders_2263_);
lean_inc_ref(v_modifiers_2261_);
lean_inc(v_levelParams_2260_);
lean_inc(v_ref_2258_);
v_perms_2270_ = lean_ctor_get(v_fixedParamPerms_2247_, 1);
lean_inc_ref(v_perms_2270_);
v___x_2271_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2272_ = lean_box(v___x_2269_);
v___x_2273_ = lean_box(v_kind_2259_);
lean_inc_ref(v_perms_2270_);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 21, 15);
lean_closure_set(v___f_2274_, 0, v_preDefs_2249_);
lean_closure_set(v___f_2274_, 1, v_perms_2270_);
lean_closure_set(v___f_2274_, 2, v___x_2256_);
lean_closure_set(v___f_2274_, 3, v_argsPacker_2248_);
lean_closure_set(v___f_2274_, 4, v___x_2272_);
lean_closure_set(v___f_2274_, 5, v_ref_2258_);
lean_closure_set(v___f_2274_, 6, v___x_2273_);
lean_closure_set(v___f_2274_, 7, v_levelParams_2260_);
lean_closure_set(v___f_2274_, 8, v_modifiers_2261_);
lean_closure_set(v___f_2274_, 9, v_newFn_2268_);
lean_closure_set(v___f_2274_, 10, v_binders_2263_);
lean_closure_set(v___f_2274_, 11, v_numSectionVars_2264_);
lean_closure_set(v___f_2274_, 12, v_value_2266_);
lean_closure_set(v___f_2274_, 13, v_termination_2267_);
lean_closure_set(v___f_2274_, 14, v_fixedParamPerms_2247_);
v___x_2275_ = lean_array_get(v___x_2271_, v_perms_2270_, v___x_2256_);
lean_dec_ref(v_perms_2270_);
v___x_2276_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2275_, v_type_2265_, v___f_2274_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; 
lean_inc(v___x_2257_);
lean_dec(v_newFn_2268_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec_ref(v_preDefs_2249_);
lean_dec_ref(v_argsPacker_2248_);
lean_dec_ref(v_fixedParamPerms_2247_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2257_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2278_, lean_object* v_argsPacker_2279_, lean_object* v_preDefs_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2278_, v_argsPacker_2279_, v_preDefs_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2287_, lean_object* v_ys_2288_, lean_object* v_as_2289_, lean_object* v_i_2290_, lean_object* v_j_2291_, lean_object* v_inv_2292_, lean_object* v_bs_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2287_, v_ys_2288_, v_as_2289_, v_i_2290_, v_j_2291_, v_bs_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2300_, lean_object* v_ys_2301_, lean_object* v_as_2302_, lean_object* v_i_2303_, lean_object* v_j_2304_, lean_object* v_inv_2305_, lean_object* v_bs_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2300_, v_ys_2301_, v_as_2302_, v_i_2303_, v_j_2304_, v_inv_2305_, v_bs_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec_ref(v_as_2302_);
lean_dec_ref(v___x_2300_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2313_, lean_object* v_ys_2314_, lean_object* v_as_2315_, lean_object* v_i_2316_, lean_object* v_j_2317_, lean_object* v_inv_2318_, lean_object* v_bs_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2313_, v_ys_2314_, v_as_2315_, v_i_2316_, v_j_2317_, v_bs_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2326_, lean_object* v_ys_2327_, lean_object* v_as_2328_, lean_object* v_i_2329_, lean_object* v_j_2330_, lean_object* v_inv_2331_, lean_object* v_bs_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2326_, v_ys_2327_, v_as_2328_, v_i_2329_, v_j_2330_, v_inv_2331_, v_bs_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec_ref(v_as_2328_);
lean_dec_ref(v___x_2326_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2339_, lean_object* v_k_2340_, uint8_t v_cleanupAnnotations_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___f_2347_; uint8_t v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2347_, 0, v_k_2340_);
v___x_2348_ = 1;
v___x_2349_ = 0;
v___x_2350_ = lean_box(0);
v___x_2351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2339_, v___x_2348_, v___x_2349_, v___x_2348_, v___x_2349_, v___x_2350_, v___f_2347_, v_cleanupAnnotations_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2351_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2351_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2368_, lean_object* v_k_2369_, lean_object* v_cleanupAnnotations_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2376_; lean_object* v_res_2377_; 
v_cleanupAnnotations_boxed_2376_ = lean_unbox(v_cleanupAnnotations_2370_);
v_res_2377_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2368_, v_k_2369_, v_cleanupAnnotations_boxed_2376_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2378_, lean_object* v_e_2379_, lean_object* v_k_2380_, uint8_t v_cleanupAnnotations_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2379_, v_k_2380_, v_cleanupAnnotations_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2388_, lean_object* v_e_2389_, lean_object* v_k_2390_, lean_object* v_cleanupAnnotations_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2397_; lean_object* v_res_2398_; 
v_cleanupAnnotations_boxed_2397_ = lean_unbox(v_cleanupAnnotations_2391_);
v_res_2398_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2388_, v_e_2389_, v_k_2390_, v_cleanupAnnotations_boxed_2397_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___f_2405_; lean_object* v___x_1907__overap_2406_; lean_object* v___x_2407_; 
v___f_2405_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1907__overap_2406_ = lean_panic_fn(v___f_2405_, v_msg_2399_);
v___x_2407_ = lean_apply_5(v___x_1907__overap_2406_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, lean_box(0));
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_array_get_size(v_xs_2415_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2424_, v_x_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v_x_2425_);
lean_dec_ref(v_xs_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2432_, size_t v_sz_2433_, size_t v_i_2434_, lean_object* v_b_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_a_2441_; uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_lt(v_i_2434_, v_sz_2433_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v___y_2436_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_b_2435_);
return v___x_2446_;
}
else
{
lean_object* v_snd_2447_; lean_object* v_fst_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2492_; 
v_snd_2447_ = lean_ctor_get(v_b_2435_, 1);
v_fst_2448_ = lean_ctor_get(v_b_2435_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_b_2435_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2450_ = v_b_2435_;
v_isShared_2451_ = v_isSharedCheck_2492_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snd_2447_);
lean_inc(v_fst_2448_);
lean_dec(v_b_2435_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2492_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_array_2452_; lean_object* v_start_2453_; lean_object* v_stop_2454_; uint8_t v___x_2455_; 
v_array_2452_ = lean_ctor_get(v_snd_2447_, 0);
v_start_2453_ = lean_ctor_get(v_snd_2447_, 1);
v_stop_2454_ = lean_ctor_get(v_snd_2447_, 2);
v___x_2455_ = lean_nat_dec_lt(v_start_2453_, v_stop_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v___y_2436_);
if (v_isShared_2451_ == 0)
{
v___x_2457_ = v___x_2450_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_fst_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_snd_2447_);
v___x_2457_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
else
{
lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2488_; 
lean_inc(v_stop_2454_);
lean_inc(v_start_2453_);
lean_inc_ref(v_array_2452_);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_snd_2447_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; lean_object* v_unused_2490_; lean_object* v_unused_2491_; 
v_unused_2489_ = lean_ctor_get(v_snd_2447_, 2);
lean_dec(v_unused_2489_);
v_unused_2490_ = lean_ctor_get(v_snd_2447_, 1);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_snd_2447_, 0);
lean_dec(v_unused_2491_);
v___x_2461_ = v_snd_2447_;
v_isShared_2462_ = v_isSharedCheck_2488_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v_snd_2447_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2488_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2463_ = lean_array_fget(v_array_2452_, v_start_2453_);
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2465_ = lean_nat_add(v_start_2453_, v___x_2464_);
lean_dec(v_start_2453_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v___x_2465_);
v___x_2467_ = v___x_2461_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_array_2452_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_stop_2454_);
v___x_2467_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_a_2468_ = lean_array_uget_borrowed(v_as_2432_, v_i_2434_);
v___x_2469_ = l_Lean_Expr_fvarId_x21(v_a_2468_);
lean_inc_ref(v___y_2436_);
v___x_2470_ = l_Lean_FVarId_getUserName___redArg(v___x_2469_, v___y_2436_, v___y_2437_, v___y_2438_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = lean_array_push(v_fst_2448_, v_a_2471_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2467_);
lean_ctor_set(v___x_2450_, 0, v___x_2472_);
v___x_2474_ = v___x_2450_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2467_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
v_a_2441_ = v___x_2474_;
goto v___jp_2440_;
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v___x_2467_);
lean_del_object(v___x_2450_);
lean_dec(v_fst_2448_);
lean_dec_ref(v___y_2436_);
v_a_2476_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2470_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2470_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v___x_2485_; 
lean_dec_ref(v___x_2463_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2467_);
v___x_2485_ = v___x_2450_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_fst_2448_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2467_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
v_a_2441_ = v___x_2485_;
goto v___jp_2440_;
}
}
}
}
}
}
}
v___jp_2440_:
{
size_t v___x_2442_; size_t v___x_2443_; 
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2434_, v___x_2442_);
v_i_2434_ = v___x_2443_;
v_b_2435_ = v_a_2441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
size_t v_sz_boxed_2501_; size_t v_i_boxed_2502_; lean_object* v_res_2503_; 
v_sz_boxed_2501_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2502_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2493_, v_sz_boxed_2501_, v_i_boxed_2502_, v_b_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v_as_2493_);
return v_res_2503_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2506_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2507_ = lean_unsigned_to_nat(4u);
v___x_2508_ = lean_unsigned_to_nat(119u);
v___x_2509_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2510_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2511_ = l_mkPanicMessageWithDecl(v___x_2510_, v___x_2509_, v___x_2508_, v___x_2507_, v___x_2506_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2513_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2514_ = lean_unsigned_to_nat(4u);
v___x_2515_ = lean_unsigned_to_nat(120u);
v___x_2516_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2517_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2518_ = l_mkPanicMessageWithDecl(v___x_2517_, v___x_2516_, v___x_2515_, v___x_2514_, v___x_2513_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2521_, lean_object* v_fixedParamPerms_2522_, lean_object* v_preDefIdx_2523_, lean_object* v_xs_2524_, lean_object* v_x_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = lean_array_get_size(v_xs_2524_);
v___x_2532_ = lean_nat_dec_eq(v___x_2531_, v_a_2521_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2534_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2533_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2534_;
}
else
{
lean_object* v_perms_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_perms_2535_ = lean_ctor_get(v_fixedParamPerms_2522_, 1);
v___x_2536_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2537_ = lean_array_get_borrowed(v___x_2536_, v_perms_2535_, v_preDefIdx_2523_);
v___x_2538_ = lean_array_get_size(v___x_2537_);
v___x_2539_ = lean_nat_dec_eq(v___x_2538_, v_a_2521_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2541_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2540_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v___y_2527_);
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2537_);
v___x_2544_ = l_Array_toSubarray___redArg(v___x_2537_, v___x_2542_, v___x_2538_);
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v_sz_2546_ = lean_array_size(v_xs_2524_);
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2524_, v_sz_2546_, v___x_2547_, v___x_2545_, v___y_2526_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2557_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_fst_2553_; lean_object* v___x_2555_; 
v_fst_2553_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_fst_2553_);
lean_dec(v_a_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_fst_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_fst_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_a_2558_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2548_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2548_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2566_, lean_object* v_fixedParamPerms_2567_, lean_object* v_preDefIdx_2568_, lean_object* v_xs_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2566_, v_fixedParamPerms_2567_, v_preDefIdx_2568_, v_xs_2569_, v_x_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec_ref(v_x_2570_);
lean_dec_ref(v_xs_2569_);
lean_dec(v_preDefIdx_2568_);
lean_dec_ref(v_fixedParamPerms_2567_);
lean_dec(v_a_2566_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2578_, lean_object* v_preDefIdx_2579_, lean_object* v_preDef_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_type_2586_; lean_object* v_value_2587_; lean_object* v___f_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; 
v_type_2586_ = lean_ctor_get(v_preDef_2580_, 6);
lean_inc_ref(v_type_2586_);
v_value_2587_ = lean_ctor_get(v_preDef_2580_, 7);
lean_inc_ref(v_value_2587_);
lean_dec_ref(v_preDef_2580_);
v___f_2588_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2589_ = 0;
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2590_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2587_, v___f_2588_, v___x_2589_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
lean_inc(v_a_2591_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2592_, 0, v_a_2591_);
lean_closure_set(v___f_2592_, 1, v_fixedParamPerms_2578_);
lean_closure_set(v___f_2592_, 2, v_preDefIdx_2579_);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_a_2591_);
v___x_2594_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2586_, v___x_2593_, v___f_2592_, v___x_2589_, v___x_2589_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
return v___x_2594_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_type_2586_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_preDefIdx_2579_);
lean_dec_ref(v_fixedParamPerms_2578_);
v_a_2595_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2590_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2590_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2603_, lean_object* v_preDefIdx_2604_, lean_object* v_preDef_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2603_, v_preDefIdx_2604_, v_preDef_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2612_, size_t v_sz_2613_, size_t v_i_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2612_, v_sz_2613_, v_i_2614_, v_b_2615_, v___y_2616_, v___y_2618_, v___y_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2622_, lean_object* v_sz_2623_, lean_object* v_i_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
size_t v_sz_boxed_2631_; size_t v_i_boxed_2632_; lean_object* v_res_2633_; 
v_sz_boxed_2631_ = lean_unbox_usize(v_sz_2623_);
lean_dec(v_sz_2623_);
v_i_boxed_2632_ = lean_unbox_usize(v_i_2624_);
lean_dec(v_i_2624_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2622_, v_sz_boxed_2631_, v_i_boxed_2632_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v_as_2622_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___f_2640_; lean_object* v___x_1231__overap_2641_; lean_object* v___x_2642_; 
v___f_2640_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1231__overap_2641_ = lean_panic_fn(v___f_2640_, v_msg_2634_);
v___x_2642_ = lean_apply_5(v___x_1231__overap_2641_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, lean_box(0));
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg(lean_object* v_cls_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_options_2656_; uint8_t v_hasTrace_2657_; 
v_options_2656_ = lean_ctor_get(v___y_2654_, 2);
v_hasTrace_2657_ = lean_ctor_get_uint8(v_options_2656_, sizeof(void*)*1);
if (v_hasTrace_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec(v_cls_2653_);
v___x_2658_ = lean_box(v_hasTrace_2657_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
else
{
lean_object* v_inheritedTraceOptions_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_inheritedTraceOptions_2660_ = lean_ctor_get(v___y_2654_, 13);
v___x_2661_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___closed__1));
v___x_2662_ = l_Lean_Name_append(v___x_2661_, v_cls_2653_);
v___x_2663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2660_, v_options_2656_, v___x_2662_);
lean_dec(v___x_2662_);
v___x_2664_ = lean_box(v___x_2663_);
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg___boxed(lean_object* v_cls_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg(v_cls_2666_, v___y_2667_);
lean_dec_ref(v___y_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg(v_cls_2670_, v___y_2673_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2683_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2686_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__1));
v___x_2687_ = lean_unsigned_to_nat(8u);
v___x_2688_ = lean_unsigned_to_nat(135u);
v___x_2689_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__0));
v___x_2690_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2691_ = l_mkPanicMessageWithDecl(v___x_2690_, v___x_2689_, v___x_2688_, v___x_2687_, v___x_2686_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0(lean_object* v___x_2692_, lean_object* v_unaryPreDefNonRec_2693_, lean_object* v___x_2694_, lean_object* v_us_2695_, lean_object* v_argsPacker_2696_, lean_object* v_j_2697_, uint8_t v_isZero_2698_, lean_object* v_params_2699_, lean_object* v_x_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = lean_array_get_size(v_params_2699_);
v___x_2707_ = lean_nat_dec_eq(v___x_2692_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_j_2697_);
lean_dec(v_us_2695_);
lean_dec_ref(v_unaryPreDefNonRec_2693_);
v___x_2708_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___closed__2);
v___x_2709_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2708_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2709_;
}
else
{
lean_object* v_declName_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_declName_2710_ = lean_ctor_get(v_unaryPreDefNonRec_2693_, 3);
lean_inc(v_declName_2710_);
lean_dec_ref(v_unaryPreDefNonRec_2693_);
v___x_2711_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2694_, v_params_2699_);
v___x_2712_ = l_Lean_mkConst(v_declName_2710_, v_us_2695_);
v___x_2713_ = l_Lean_mkAppN(v___x_2712_, v___x_2711_);
lean_dec_ref(v___x_2711_);
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
v___x_2714_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2696_, v___x_2713_, v_j_2697_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2694_, v_params_2699_);
v___x_2717_ = l_Lean_Expr_beta(v_a_2715_, v___x_2716_);
v___x_2718_ = 1;
v___x_2719_ = l_Lean_Meta_mkLambdaFVars(v_params_2699_, v___x_2717_, v_isZero_2698_, v___x_2707_, v_isZero_2698_, v___x_2707_, v___x_2718_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v___x_2719_;
}
else
{
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v___x_2714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___boxed(lean_object* v___x_2720_, lean_object* v_unaryPreDefNonRec_2721_, lean_object* v___x_2722_, lean_object* v_us_2723_, lean_object* v_argsPacker_2724_, lean_object* v_j_2725_, lean_object* v_isZero_2726_, lean_object* v_params_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v_isZero_boxed_2734_; lean_object* v_res_2735_; 
v_isZero_boxed_2734_ = lean_unbox(v_isZero_2726_);
v_res_2735_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0(v___x_2720_, v_unaryPreDefNonRec_2721_, v___x_2722_, v_us_2723_, v_argsPacker_2724_, v_j_2725_, v_isZero_boxed_2734_, v_params_2727_, v_x_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v_x_2728_);
lean_dec_ref(v_params_2727_);
lean_dec_ref(v_argsPacker_2724_);
lean_dec_ref(v___x_2722_);
lean_dec(v___x_2720_);
return v_res_2735_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2736_; double v___x_2737_; 
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = lean_float_of_nat(v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_cls_2741_, lean_object* v_msg_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_ref_2748_; lean_object* v___x_2749_; lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2794_; 
v_ref_2748_ = lean_ctor_get(v___y_2745_, 5);
v___x_2749_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2794_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2794_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v_traceState_2755_; lean_object* v_env_2756_; lean_object* v_nextMacroScope_2757_; lean_object* v_ngen_2758_; lean_object* v_auxDeclNGen_2759_; lean_object* v_cache_2760_; lean_object* v_messages_2761_; lean_object* v_infoState_2762_; lean_object* v_snapshotTasks_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2793_; 
v___x_2754_ = lean_st_ref_take(v___y_2746_);
v_traceState_2755_ = lean_ctor_get(v___x_2754_, 4);
v_env_2756_ = lean_ctor_get(v___x_2754_, 0);
v_nextMacroScope_2757_ = lean_ctor_get(v___x_2754_, 1);
v_ngen_2758_ = lean_ctor_get(v___x_2754_, 2);
v_auxDeclNGen_2759_ = lean_ctor_get(v___x_2754_, 3);
v_cache_2760_ = lean_ctor_get(v___x_2754_, 5);
v_messages_2761_ = lean_ctor_get(v___x_2754_, 6);
v_infoState_2762_ = lean_ctor_get(v___x_2754_, 7);
v_snapshotTasks_2763_ = lean_ctor_get(v___x_2754_, 8);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2765_ = v___x_2754_;
v_isShared_2766_ = v_isSharedCheck_2793_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_snapshotTasks_2763_);
lean_inc(v_infoState_2762_);
lean_inc(v_messages_2761_);
lean_inc(v_cache_2760_);
lean_inc(v_traceState_2755_);
lean_inc(v_auxDeclNGen_2759_);
lean_inc(v_ngen_2758_);
lean_inc(v_nextMacroScope_2757_);
lean_inc(v_env_2756_);
lean_dec(v___x_2754_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2793_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
uint64_t v_tid_2767_; lean_object* v_traces_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2792_; 
v_tid_2767_ = lean_ctor_get_uint64(v_traceState_2755_, sizeof(void*)*1);
v_traces_2768_ = lean_ctor_get(v_traceState_2755_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_traceState_2755_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2770_ = v_traceState_2755_;
v_isShared_2771_ = v_isSharedCheck_2792_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_traces_2768_);
lean_dec(v_traceState_2755_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2792_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; double v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__0);
v___x_2774_ = 0;
v___x_2775_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__1));
v___x_2776_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2776_, 0, v_cls_2741_);
lean_ctor_set(v___x_2776_, 1, v___x_2772_);
lean_ctor_set(v___x_2776_, 2, v___x_2775_);
lean_ctor_set_float(v___x_2776_, sizeof(void*)*3, v___x_2773_);
lean_ctor_set_float(v___x_2776_, sizeof(void*)*3 + 8, v___x_2773_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*3 + 16, v___x_2774_);
v___x_2777_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___closed__2));
v___x_2778_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v_a_2750_);
lean_ctor_set(v___x_2778_, 2, v___x_2777_);
lean_inc(v_ref_2748_);
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_ref_2748_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_PersistentArray_push___redArg(v_traces_2768_, v___x_2779_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2780_);
v___x_2782_ = v___x_2770_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2780_);
lean_ctor_set_uint64(v_reuseFailAlloc_2791_, sizeof(void*)*1, v_tid_2767_);
v___x_2782_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2784_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v___x_2782_);
v___x_2784_ = v___x_2765_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_env_2756_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_nextMacroScope_2757_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_ngen_2758_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v_auxDeclNGen_2759_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 5, v_cache_2760_);
lean_ctor_set(v_reuseFailAlloc_2790_, 6, v_messages_2761_);
lean_ctor_set(v_reuseFailAlloc_2790_, 7, v_infoState_2762_);
lean_ctor_set(v_reuseFailAlloc_2790_, 8, v_snapshotTasks_2763_);
v___x_2784_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = lean_st_ref_set(v___y_2746_, v___x_2784_);
v___x_2786_ = lean_box(0);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2786_);
v___x_2788_ = v___x_2752_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_cls_2795_, lean_object* v_msg_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_cls_2795_, v_msg_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2802_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__4));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_fixedParamPerms_2813_, lean_object* v_unaryPreDefNonRec_2814_, lean_object* v_us_2815_, lean_object* v_argsPacker_2816_, lean_object* v_as_2817_, lean_object* v_i_2818_, lean_object* v_j_2819_, lean_object* v_bs_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_zero_2826_; uint8_t v_isZero_2827_; 
v_zero_2826_ = lean_unsigned_to_nat(0u);
v_isZero_2827_ = lean_nat_dec_eq(v_i_2818_, v_zero_2826_);
if (v_isZero_2827_ == 1)
{
lean_object* v___x_2828_; 
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v_j_2819_);
lean_dec(v_i_2818_);
lean_dec_ref(v_argsPacker_2816_);
lean_dec(v_us_2815_);
lean_dec_ref(v_unaryPreDefNonRec_2814_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_bs_2820_);
return v___x_2828_;
}
else
{
lean_object* v_perms_2829_; lean_object* v___x_2830_; lean_object* v_ref_2831_; uint8_t v_kind_2832_; lean_object* v_levelParams_2833_; lean_object* v_modifiers_2834_; lean_object* v_declName_2835_; lean_object* v_binders_2836_; lean_object* v_numSectionVars_2837_; lean_object* v_type_2838_; lean_object* v_termination_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2886_; 
v_perms_2829_ = lean_ctor_get(v_fixedParamPerms_2813_, 1);
v___x_2830_ = lean_array_fget(v_as_2817_, v_j_2819_);
v_ref_2831_ = lean_ctor_get(v___x_2830_, 0);
v_kind_2832_ = lean_ctor_get_uint8(v___x_2830_, sizeof(void*)*9);
v_levelParams_2833_ = lean_ctor_get(v___x_2830_, 1);
v_modifiers_2834_ = lean_ctor_get(v___x_2830_, 2);
v_declName_2835_ = lean_ctor_get(v___x_2830_, 3);
v_binders_2836_ = lean_ctor_get(v___x_2830_, 4);
v_numSectionVars_2837_ = lean_ctor_get(v___x_2830_, 5);
v_type_2838_ = lean_ctor_get(v___x_2830_, 6);
v_termination_2839_ = lean_ctor_get(v___x_2830_, 8);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2830_, 7);
lean_dec(v_unused_2887_);
v___x_2841_ = v___x_2830_;
v_isShared_2842_ = v_isSharedCheck_2886_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_termination_2839_);
lean_inc(v_type_2838_);
lean_inc(v_numSectionVars_2837_);
lean_inc(v_binders_2836_);
lean_inc(v_declName_2835_);
lean_inc(v_modifiers_2834_);
lean_inc(v_levelParams_2833_);
lean_inc(v_ref_2831_);
lean_dec(v___x_2830_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2886_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2843_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2844_ = lean_array_get_borrowed(v___x_2843_, v_perms_2829_, v_j_2819_);
v___x_2845_ = lean_array_get_size(v___x_2844_);
v___x_2846_ = lean_box(v_isZero_2827_);
lean_inc(v_j_2819_);
lean_inc_ref(v_argsPacker_2816_);
lean_inc(v_us_2815_);
lean_inc(v___x_2844_);
lean_inc_ref(v_unaryPreDefNonRec_2814_);
v___f_2847_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2847_, 0, v___x_2845_);
lean_closure_set(v___f_2847_, 1, v_unaryPreDefNonRec_2814_);
lean_closure_set(v___f_2847_, 2, v___x_2844_);
lean_closure_set(v___f_2847_, 3, v_us_2815_);
lean_closure_set(v___f_2847_, 4, v_argsPacker_2816_);
lean_closure_set(v___f_2847_, 5, v_j_2819_);
lean_closure_set(v___f_2847_, 6, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2845_);
lean_inc(v___y_2824_);
lean_inc_ref(v___y_2823_);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc_ref(v_type_2838_);
v___x_2849_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2838_, v___x_2848_, v___f_2847_, v_isZero_2827_, v_isZero_2827_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v_a_2853_; lean_object* v_one_2854_; lean_object* v_n_2855_; uint8_t v___x_2863_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__3));
v___x_2852_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___redArg(v___x_2851_, v___y_2823_);
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2852_);
v_one_2854_ = lean_unsigned_to_nat(1u);
v_n_2855_ = lean_nat_sub(v_i_2818_, v_one_2854_);
lean_dec(v_i_2818_);
v___x_2863_ = lean_unbox(v_a_2853_);
lean_dec(v_a_2853_);
if (v___x_2863_ == 0)
{
goto v___jp_2856_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_inc(v_declName_2835_);
v___x_2864_ = l_Lean_MessageData_ofName(v_declName_2835_);
v___x_2865_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___closed__5);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
lean_inc(v_a_2850_);
v___x_2867_ = l_Lean_MessageData_ofExpr(v_a_2850_);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v___x_2851_, v___x_2868_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref(v___x_2869_);
goto v___jp_2856_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_n_2855_);
lean_dec(v_a_2850_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_termination_2839_);
lean_dec_ref(v_type_2838_);
lean_dec(v_numSectionVars_2837_);
lean_dec(v_binders_2836_);
lean_dec(v_declName_2835_);
lean_dec_ref(v_modifiers_2834_);
lean_dec(v_levelParams_2833_);
lean_dec(v_ref_2831_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_bs_2820_);
lean_dec(v_j_2819_);
lean_dec_ref(v_argsPacker_2816_);
lean_dec(v_us_2815_);
lean_dec_ref(v_unaryPreDefNonRec_2814_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
v___jp_2856_:
{
lean_object* v___x_2858_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 7, v_a_2850_);
v___x_2858_ = v___x_2841_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_ref_2831_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_levelParams_2833_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_modifiers_2834_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_declName_2835_);
lean_ctor_set(v_reuseFailAlloc_2862_, 4, v_binders_2836_);
lean_ctor_set(v_reuseFailAlloc_2862_, 5, v_numSectionVars_2837_);
lean_ctor_set(v_reuseFailAlloc_2862_, 6, v_type_2838_);
lean_ctor_set(v_reuseFailAlloc_2862_, 7, v_a_2850_);
lean_ctor_set(v_reuseFailAlloc_2862_, 8, v_termination_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2862_, sizeof(void*)*9, v_kind_2832_);
v___x_2858_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_nat_add(v_j_2819_, v_one_2854_);
lean_dec(v_j_2819_);
v___x_2860_ = lean_array_push(v_bs_2820_, v___x_2858_);
v_i_2818_ = v_n_2855_;
v_j_2819_ = v___x_2859_;
v_bs_2820_ = v___x_2860_;
goto _start;
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_del_object(v___x_2841_);
lean_dec_ref(v_termination_2839_);
lean_dec_ref(v_type_2838_);
lean_dec(v_numSectionVars_2837_);
lean_dec(v_binders_2836_);
lean_dec(v_declName_2835_);
lean_dec_ref(v_modifiers_2834_);
lean_dec(v_levelParams_2833_);
lean_dec(v_ref_2831_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_bs_2820_);
lean_dec(v_j_2819_);
lean_dec(v_i_2818_);
lean_dec_ref(v_argsPacker_2816_);
lean_dec(v_us_2815_);
lean_dec_ref(v_unaryPreDefNonRec_2814_);
v_a_2878_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2849_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2849_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_fixedParamPerms_2888_, lean_object* v_unaryPreDefNonRec_2889_, lean_object* v_us_2890_, lean_object* v_argsPacker_2891_, lean_object* v_as_2892_, lean_object* v_i_2893_, lean_object* v_j_2894_, lean_object* v_bs_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_fixedParamPerms_2888_, v_unaryPreDefNonRec_2889_, v_us_2890_, v_argsPacker_2891_, v_as_2892_, v_i_2893_, v_j_2894_, v_bs_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec_ref(v_as_2892_);
lean_dec_ref(v_fixedParamPerms_2888_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2902_, lean_object* v_preDefs_2903_, lean_object* v_fixedParamPerms_2904_, lean_object* v_us_2905_, lean_object* v_argsPacker_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
lean_inc(v___y_2910_);
lean_inc_ref(v___y_2909_);
v___x_2912_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2902_, v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec_ref(v___x_2912_);
v___x_2913_ = lean_array_get_size(v_preDefs_2903_);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2915_ = lean_mk_empty_array_with_capacity(v___x_2913_);
v___x_2916_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_fixedParamPerms_2904_, v_unaryPreDefNonRec_2902_, v_us_2905_, v_argsPacker_2906_, v_preDefs_2903_, v___x_2913_, v___x_2914_, v___x_2915_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v_argsPacker_2906_);
lean_dec(v_us_2905_);
lean_dec_ref(v_unaryPreDefNonRec_2902_);
v_a_2917_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2912_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2912_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2925_, lean_object* v_preDefs_2926_, lean_object* v_fixedParamPerms_2927_, lean_object* v_us_2928_, lean_object* v_argsPacker_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2925_, v_preDefs_2926_, v_fixedParamPerms_2927_, v_us_2928_, v_argsPacker_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec_ref(v_fixedParamPerms_2927_);
lean_dec_ref(v_preDefs_2926_);
return v_res_2935_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__0);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
return v___x_2940_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__1);
v___x_2942_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
lean_ctor_set(v___x_2942_, 2, v___x_2941_);
lean_ctor_set(v___x_2942_, 3, v___x_2941_);
lean_ctor_set(v___x_2942_, 4, v___x_2941_);
lean_ctor_set(v___x_2942_, 5, v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(lean_object* v_env_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; lean_object* v_nextMacroScope_2948_; lean_object* v_ngen_2949_; lean_object* v_auxDeclNGen_2950_; lean_object* v_traceState_2951_; lean_object* v_messages_2952_; lean_object* v_infoState_2953_; lean_object* v_snapshotTasks_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2980_; 
v___x_2947_ = lean_st_ref_take(v___y_2945_);
v_nextMacroScope_2948_ = lean_ctor_get(v___x_2947_, 1);
v_ngen_2949_ = lean_ctor_get(v___x_2947_, 2);
v_auxDeclNGen_2950_ = lean_ctor_get(v___x_2947_, 3);
v_traceState_2951_ = lean_ctor_get(v___x_2947_, 4);
v_messages_2952_ = lean_ctor_get(v___x_2947_, 6);
v_infoState_2953_ = lean_ctor_get(v___x_2947_, 7);
v_snapshotTasks_2954_ = lean_ctor_get(v___x_2947_, 8);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; lean_object* v_unused_2982_; 
v_unused_2981_ = lean_ctor_get(v___x_2947_, 5);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v___x_2947_, 0);
lean_dec(v_unused_2982_);
v___x_2956_ = v___x_2947_;
v_isShared_2957_ = v_isSharedCheck_2980_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_snapshotTasks_2954_);
lean_inc(v_infoState_2953_);
lean_inc(v_messages_2952_);
lean_inc(v_traceState_2951_);
lean_inc(v_auxDeclNGen_2950_);
lean_inc(v_ngen_2949_);
lean_inc(v_nextMacroScope_2948_);
lean_dec(v___x_2947_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2980_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__2);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 5, v___x_2958_);
lean_ctor_set(v___x_2956_, 0, v_env_2943_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_env_2943_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_nextMacroScope_2948_);
lean_ctor_set(v_reuseFailAlloc_2979_, 2, v_ngen_2949_);
lean_ctor_set(v_reuseFailAlloc_2979_, 3, v_auxDeclNGen_2950_);
lean_ctor_set(v_reuseFailAlloc_2979_, 4, v_traceState_2951_);
lean_ctor_set(v_reuseFailAlloc_2979_, 5, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2979_, 6, v_messages_2952_);
lean_ctor_set(v_reuseFailAlloc_2979_, 7, v_infoState_2953_);
lean_ctor_set(v_reuseFailAlloc_2979_, 8, v_snapshotTasks_2954_);
v___x_2960_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v_mctx_2963_; lean_object* v_zetaDeltaFVarIds_2964_; lean_object* v_postponed_2965_; lean_object* v_diag_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2977_; 
v___x_2961_ = lean_st_ref_set(v___y_2945_, v___x_2960_);
v___x_2962_ = lean_st_ref_take(v___y_2944_);
v_mctx_2963_ = lean_ctor_get(v___x_2962_, 0);
v_zetaDeltaFVarIds_2964_ = lean_ctor_get(v___x_2962_, 2);
v_postponed_2965_ = lean_ctor_get(v___x_2962_, 3);
v_diag_2966_ = lean_ctor_get(v___x_2962_, 4);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v___x_2962_, 1);
lean_dec(v_unused_2978_);
v___x_2968_ = v___x_2962_;
v_isShared_2969_ = v_isSharedCheck_2977_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_diag_2966_);
lean_inc(v_postponed_2965_);
lean_inc(v_zetaDeltaFVarIds_2964_);
lean_inc(v_mctx_2963_);
lean_dec(v___x_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2977_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2970_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___closed__3);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_2970_);
v___x_2972_ = v___x_2968_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_mctx_2963_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_zetaDeltaFVarIds_2964_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_postponed_2965_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_diag_2966_);
v___x_2972_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_st_ref_set(v___y_2944_, v___x_2972_);
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg___boxed(lean_object* v_env_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(v_env_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec(v___y_2984_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg(lean_object* v_env_2988_, lean_object* v_x_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v_env_2996_; lean_object* v_a_2998_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_2995_ = lean_st_ref_get(v___y_2993_);
v_env_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc_ref(v_env_2996_);
lean_dec(v___x_2995_);
v___x_3008_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(v_env_2988_, v___y_2991_, v___y_2993_);
lean_dec_ref(v___x_3008_);
lean_inc(v___y_2993_);
lean_inc(v___y_2991_);
v___x_3009_ = lean_apply_5(v_x_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, lean_box(0));
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(v_env_2996_, v___y_2991_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec(v___y_2991_);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v___x_3011_, 0);
lean_dec(v_unused_3019_);
v___x_3013_ = v___x_3011_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_dec(v___x_3011_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v_a_3010_);
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3010_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
else
{
lean_object* v_a_3020_; 
v_a_3020_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3009_);
v_a_2998_ = v_a_3020_;
goto v___jp_2997_;
}
v___jp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v___x_2999_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(v_env_2996_, v___y_2991_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec(v___y_2991_);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3007_);
v___x_3001_ = v___x_2999_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v___x_2999_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 1);
lean_ctor_set(v___x_3001_, 0, v_a_2998_);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2998_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg___boxed(lean_object* v_env_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg(v_env_3021_, v_x_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3029_, lean_object* v_argsPacker_3030_, lean_object* v_preDefs_3031_, lean_object* v_unaryPreDefNonRec_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v_levelParams_3039_; lean_object* v_env_3040_; lean_object* v___x_3041_; lean_object* v_us_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3038_ = lean_st_ref_get(v_a_3036_);
v_levelParams_3039_ = lean_ctor_get(v_unaryPreDefNonRec_3032_, 1);
v_env_3040_ = lean_ctor_get(v___x_3038_, 0);
lean_inc_ref(v_env_3040_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
lean_inc(v_levelParams_3039_);
v_us_3042_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3039_, v___x_3041_);
v___f_3043_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3043_, 0, v_unaryPreDefNonRec_3032_);
lean_closure_set(v___f_3043_, 1, v_preDefs_3031_);
lean_closure_set(v___f_3043_, 2, v_fixedParamPerms_3029_);
lean_closure_set(v___f_3043_, 3, v_us_3042_);
lean_closure_set(v___f_3043_, 4, v_argsPacker_3030_);
v___x_3044_ = l_Lean_Environment_unlockAsync(v_env_3040_);
v___x_3045_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg(v___x_3044_, v___f_3043_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3046_, lean_object* v_argsPacker_3047_, lean_object* v_preDefs_3048_, lean_object* v_unaryPreDefNonRec_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3046_, v_argsPacker_3047_, v_preDefs_3048_, v_unaryPreDefNonRec_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_fixedParamPerms_3056_, lean_object* v_unaryPreDefNonRec_3057_, lean_object* v_us_3058_, lean_object* v_argsPacker_3059_, lean_object* v_as_3060_, lean_object* v_i_3061_, lean_object* v_j_3062_, lean_object* v_inv_3063_, lean_object* v_bs_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_fixedParamPerms_3056_, v_unaryPreDefNonRec_3057_, v_us_3058_, v_argsPacker_3059_, v_as_3060_, v_i_3061_, v_j_3062_, v_bs_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_fixedParamPerms_3071_, lean_object* v_unaryPreDefNonRec_3072_, lean_object* v_us_3073_, lean_object* v_argsPacker_3074_, lean_object* v_as_3075_, lean_object* v_i_3076_, lean_object* v_j_3077_, lean_object* v_inv_3078_, lean_object* v_bs_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_fixedParamPerms_3071_, v_unaryPreDefNonRec_3072_, v_us_3073_, v_argsPacker_3074_, v_as_3075_, v_i_3076_, v_j_3077_, v_inv_3078_, v_bs_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec_ref(v_as_3075_);
lean_dec_ref(v_fixedParamPerms_3071_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4(lean_object* v_env_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___redArg(v_env_3086_, v___y_3088_, v___y_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4___boxed(lean_object* v_env_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4_spec__4(v_env_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4(lean_object* v_00_u03b1_3100_, lean_object* v_env_3101_, lean_object* v_x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___redArg(v_env_3101_, v_x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4___boxed(lean_object* v_00_u03b1_3109_, lean_object* v_env_3110_, lean_object* v_x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__4(v_00_u03b1_3109_, v_env_3110_, v_x_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
return v_res_3117_;
}
}
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
