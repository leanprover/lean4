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
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.WF.preDefsFromUnaryNonRec"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: arity = params.size\n        "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_148_);
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
uint8_t v___x_2317__boxed_176_; lean_object* v_res_177_; 
v___x_2317__boxed_176_ = lean_unbox(v___x_167_);
v_res_177_ = l_Lean_Elab_WF_withAppN___lam__0(v_args_165_, v_k_166_, v___x_2317__boxed_176_, v_missing_168_, v_xs_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
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
lean_object* v___f_260_; lean_object* v___x_1474__overap_261_; lean_object* v___x_262_; 
v___f_260_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1474__overap_261_ = lean_panic_fn_borrowed(v___f_260_, v_msg_254_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_262_ = lean_apply_5(v___x_1474__overap_261_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
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
uint8_t v___x_9593__boxed_379_; size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v___x_9593__boxed_379_ = lean_unbox(v___x_375_);
v_sz_boxed_380_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_381_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_9593__boxed_379_, v_sz_boxed_380_, v_i_boxed_381_, v_bs_378_);
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
lean_object* v___y_506_; lean_object* v_fileName_515_; lean_object* v_fileMap_516_; lean_object* v_options_517_; lean_object* v_currRecDepth_518_; lean_object* v_maxRecDepth_519_; lean_object* v_ref_520_; lean_object* v_currNamespace_521_; lean_object* v_openDecls_522_; lean_object* v_initHeartbeats_523_; lean_object* v_maxHeartbeats_524_; lean_object* v_quotContext_525_; lean_object* v_currMacroScope_526_; uint8_t v_diag_527_; lean_object* v_cancelTk_x3f_528_; uint8_t v_suppressElabErrors_529_; lean_object* v_inheritedTraceOptions_530_; uint8_t v___x_531_; 
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
v___x_531_ = lean_nat_dec_eq(v_currRecDepth_518_, v_maxRecDepth_519_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_add(v_currRecDepth_518_, v___x_532_);
lean_inc_ref(v_inheritedTraceOptions_530_);
lean_inc(v_cancelTk_x3f_528_);
lean_inc(v_currMacroScope_526_);
lean_inc(v_quotContext_525_);
lean_inc(v_maxHeartbeats_524_);
lean_inc(v_initHeartbeats_523_);
lean_inc(v_openDecls_522_);
lean_inc(v_currNamespace_521_);
lean_inc(v_ref_520_);
lean_inc(v_maxRecDepth_519_);
lean_inc_ref(v_options_517_);
lean_inc_ref(v_fileMap_516_);
lean_inc_ref(v_fileName_515_);
v___x_534_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_534_, 0, v_fileName_515_);
lean_ctor_set(v___x_534_, 1, v_fileMap_516_);
lean_ctor_set(v___x_534_, 2, v_options_517_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
lean_ctor_set(v___x_534_, 4, v_maxRecDepth_519_);
lean_ctor_set(v___x_534_, 5, v_ref_520_);
lean_ctor_set(v___x_534_, 6, v_currNamespace_521_);
lean_ctor_set(v___x_534_, 7, v_openDecls_522_);
lean_ctor_set(v___x_534_, 8, v_initHeartbeats_523_);
lean_ctor_set(v___x_534_, 9, v_maxHeartbeats_524_);
lean_ctor_set(v___x_534_, 10, v_quotContext_525_);
lean_ctor_set(v___x_534_, 11, v_currMacroScope_526_);
lean_ctor_set(v___x_534_, 12, v_cancelTk_x3f_528_);
lean_ctor_set(v___x_534_, 13, v_inheritedTraceOptions_530_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*14, v_diag_527_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*14 + 1, v_suppressElabErrors_529_);
lean_inc(v___y_503_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
v___x_535_ = lean_apply_6(v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___x_534_, v___y_503_, lean_box(0));
v___y_506_ = v___x_535_;
goto v___jp_505_;
}
else
{
lean_object* v___x_536_; 
lean_dec_ref(v_x_498_);
lean_inc(v_ref_520_);
v___x_536_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_520_);
v___y_506_ = v___x_536_;
goto v___jp_505_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_545_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_559_, lean_object* v___y_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; 
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_560_);
v___x_567_ = lean_apply_7(v_k_559_, v_b_561_, v___y_560_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, lean_box(0));
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_568_, lean_object* v___y_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_568_, v___y_569_, v_b_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_577_, lean_object* v_type_578_, lean_object* v_val_579_, lean_object* v_k_580_, uint8_t v_nondep_581_, uint8_t v_kind_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___f_589_; lean_object* v___x_590_; 
lean_inc(v___y_583_);
v___f_589_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_589_, 0, v_k_580_);
lean_closure_set(v___f_589_, 1, v___y_583_);
v___x_590_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_577_, v_type_578_, v_val_579_, v___f_589_, v_nondep_581_, v_kind_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_590_) == 0)
{
return v___x_590_;
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_599_, lean_object* v_type_600_, lean_object* v_val_601_, lean_object* v_k_602_, lean_object* v_nondep_603_, lean_object* v_kind_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_nondep_boxed_611_; uint8_t v_kind_boxed_612_; lean_object* v_res_613_; 
v_nondep_boxed_611_ = lean_unbox(v_nondep_603_);
v_kind_boxed_612_ = lean_unbox(v_kind_604_);
v_res_613_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_599_, v_type_600_, v_val_601_, v_k_602_, v_nondep_boxed_611_, v_kind_boxed_612_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_614_, uint8_t v_bi_615_, lean_object* v_type_616_, lean_object* v_k_617_, uint8_t v_kind_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_626_; 
lean_inc(v___y_619_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_625_, 0, v_k_617_);
lean_closure_set(v___f_625_, 1, v___y_619_);
v___x_626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_614_, v_bi_615_, v_type_616_, v___f_625_, v_kind_618_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_626_) == 0)
{
return v___x_626_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_635_, lean_object* v_bi_636_, lean_object* v_type_637_, lean_object* v_k_638_, lean_object* v_kind_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
uint8_t v_bi_boxed_646_; uint8_t v_kind_boxed_647_; lean_object* v_res_648_; 
v_bi_boxed_646_ = lean_unbox(v_bi_636_);
v_kind_boxed_647_ = lean_unbox(v_kind_639_);
v_res_648_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_635_, v_bi_boxed_646_, v_type_637_, v_k_638_, v_kind_boxed_647_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_649_, lean_object* v_x_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_apply_1(v_x_650_, lean_box(0));
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_658_, lean_object* v_x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_658_, v_x_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_666_, lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_box(0);
return v___x_668_;
}
else
{
lean_object* v_key_669_; lean_object* v_value_670_; lean_object* v_tail_671_; uint8_t v___x_672_; 
v_key_669_ = lean_ctor_get(v_x_667_, 0);
v_value_670_ = lean_ctor_get(v_x_667_, 1);
v_tail_671_ = lean_ctor_get(v_x_667_, 2);
v___x_672_ = l_Lean_ExprStructEq_beq(v_key_669_, v_a_666_);
if (v___x_672_ == 0)
{
v_x_667_ = v_tail_671_;
goto _start;
}
else
{
lean_object* v___x_674_; 
lean_inc(v_value_670_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_value_670_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_675_, v_x_676_);
lean_dec(v_x_676_);
lean_dec_ref(v_a_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_buckets_680_; lean_object* v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v_fold_685_; uint64_t v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_buckets_680_ = lean_ctor_get(v_m_678_, 1);
v___x_681_ = lean_array_get_size(v_buckets_680_);
v___x_682_ = l_Lean_ExprStructEq_hash(v_a_679_);
v___x_683_ = 32ULL;
v___x_684_ = lean_uint64_shift_right(v___x_682_, v___x_683_);
v_fold_685_ = lean_uint64_xor(v___x_682_, v___x_684_);
v___x_686_ = 16ULL;
v___x_687_ = lean_uint64_shift_right(v_fold_685_, v___x_686_);
v___x_688_ = lean_uint64_xor(v_fold_685_, v___x_687_);
v___x_689_ = lean_uint64_to_usize(v___x_688_);
v___x_690_ = lean_usize_of_nat(v___x_681_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_sub(v___x_690_, v___x_691_);
v___x_693_ = lean_usize_land(v___x_689_, v___x_692_);
v___x_694_ = lean_array_uget_borrowed(v_buckets_680_, v___x_693_);
v___x_695_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_679_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_696_, v_a_697_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_m_696_);
return v_res_698_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
else
{
lean_object* v_key_702_; lean_object* v_tail_703_; uint8_t v___x_704_; 
v_key_702_ = lean_ctor_get(v_x_700_, 0);
v_tail_703_ = lean_ctor_get(v_x_700_, 2);
v___x_704_ = l_Lean_ExprStructEq_beq(v_key_702_, v_a_699_);
if (v___x_704_ == 0)
{
v_x_700_ = v_tail_703_;
goto _start;
}
else
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_a_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
return v_x_710_;
}
else
{
lean_object* v_key_712_; lean_object* v_value_713_; lean_object* v_tail_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_737_; 
v_key_712_ = lean_ctor_get(v_x_711_, 0);
v_value_713_ = lean_ctor_get(v_x_711_, 1);
v_tail_714_ = lean_ctor_get(v_x_711_, 2);
v_isSharedCheck_737_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_737_ == 0)
{
v___x_716_ = v_x_711_;
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_tail_714_);
lean_inc(v_value_713_);
lean_inc(v_key_712_);
lean_dec(v_x_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v_fold_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_718_ = lean_array_get_size(v_x_710_);
v___x_719_ = l_Lean_ExprStructEq_hash(v_key_712_);
v___x_720_ = 32ULL;
v___x_721_ = lean_uint64_shift_right(v___x_719_, v___x_720_);
v_fold_722_ = lean_uint64_xor(v___x_719_, v___x_721_);
v___x_723_ = 16ULL;
v___x_724_ = lean_uint64_shift_right(v_fold_722_, v___x_723_);
v___x_725_ = lean_uint64_xor(v_fold_722_, v___x_724_);
v___x_726_ = lean_uint64_to_usize(v___x_725_);
v___x_727_ = lean_usize_of_nat(v___x_718_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_sub(v___x_727_, v___x_728_);
v___x_730_ = lean_usize_land(v___x_726_, v___x_729_);
v___x_731_ = lean_array_uget_borrowed(v_x_710_, v___x_730_);
lean_inc(v___x_731_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_731_);
v___x_733_ = v___x_716_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_key_712_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_value_713_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v___x_731_);
v___x_733_ = v_reuseFailAlloc_736_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_array_uset(v_x_710_, v___x_730_, v___x_733_);
v_x_710_ = v___x_734_;
v_x_711_ = v_tail_714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_738_, lean_object* v_source_739_, lean_object* v_target_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_source_739_);
v___x_742_ = lean_nat_dec_lt(v_i_738_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec_ref(v_source_739_);
lean_dec(v_i_738_);
return v_target_740_;
}
else
{
lean_object* v_es_743_; lean_object* v___x_744_; lean_object* v_source_745_; lean_object* v_target_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_es_743_ = lean_array_fget(v_source_739_, v_i_738_);
v___x_744_ = lean_box(0);
v_source_745_ = lean_array_fset(v_source_739_, v_i_738_, v___x_744_);
v_target_746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_740_, v_es_743_);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_i_738_, v___x_747_);
lean_dec(v_i_738_);
v_i_738_ = v___x_748_;
v_source_739_ = v_source_745_;
v_target_740_ = v_target_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_nbuckets_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_751_ = lean_array_get_size(v_data_750_);
v___x_752_ = lean_unsigned_to_nat(2u);
v_nbuckets_753_ = lean_nat_mul(v___x_751_, v___x_752_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_box(0);
v___x_756_ = lean_mk_array(v_nbuckets_753_, v___x_755_);
v___x_757_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_754_, v_data_750_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_758_, lean_object* v_b_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_dec(v_b_759_);
lean_dec_ref(v_a_758_);
return v_x_760_;
}
else
{
lean_object* v_key_761_; lean_object* v_value_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_775_; 
v_key_761_ = lean_ctor_get(v_x_760_, 0);
v_value_762_ = lean_ctor_get(v_x_760_, 1);
v_tail_763_ = lean_ctor_get(v_x_760_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_775_ == 0)
{
v___x_765_ = v_x_760_;
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_value_762_);
lean_inc(v_key_761_);
lean_dec(v_x_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_775_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_ExprStructEq_beq(v_key_761_, v_a_758_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_758_, v_b_759_, v_tail_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 2, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_key_761_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_value_762_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_value_762_);
lean_dec(v_key_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_b_759_);
lean_ctor_set(v___x_765_, 0, v_a_758_);
v___x_773_ = v___x_765_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_b_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_tail_763_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_b_778_){
_start:
{
lean_object* v_size_779_; lean_object* v_buckets_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_823_; 
v_size_779_ = lean_ctor_get(v_m_776_, 0);
v_buckets_780_ = lean_ctor_get(v_m_776_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_m_776_);
if (v_isSharedCheck_823_ == 0)
{
v___x_782_ = v_m_776_;
v_isShared_783_ = v_isSharedCheck_823_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_buckets_780_);
lean_inc(v_size_779_);
lean_dec(v_m_776_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_823_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v_fold_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v_bkt_797_; uint8_t v___x_798_; 
v___x_784_ = lean_array_get_size(v_buckets_780_);
v___x_785_ = l_Lean_ExprStructEq_hash(v_a_777_);
v___x_786_ = 32ULL;
v___x_787_ = lean_uint64_shift_right(v___x_785_, v___x_786_);
v_fold_788_ = lean_uint64_xor(v___x_785_, v___x_787_);
v___x_789_ = 16ULL;
v___x_790_ = lean_uint64_shift_right(v_fold_788_, v___x_789_);
v___x_791_ = lean_uint64_xor(v_fold_788_, v___x_790_);
v___x_792_ = lean_uint64_to_usize(v___x_791_);
v___x_793_ = lean_usize_of_nat(v___x_784_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_sub(v___x_793_, v___x_794_);
v___x_796_ = lean_usize_land(v___x_792_, v___x_795_);
v_bkt_797_ = lean_array_uget_borrowed(v_buckets_780_, v___x_796_);
v___x_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_777_, v_bkt_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v_size_x27_800_; lean_object* v___x_801_; lean_object* v_buckets_x27_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v_size_x27_800_ = lean_nat_add(v_size_779_, v___x_799_);
lean_dec(v_size_779_);
lean_inc(v_bkt_797_);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v_a_777_);
lean_ctor_set(v___x_801_, 1, v_b_778_);
lean_ctor_set(v___x_801_, 2, v_bkt_797_);
v_buckets_x27_802_ = lean_array_uset(v_buckets_780_, v___x_796_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(4u);
v___x_804_ = lean_nat_mul(v_size_x27_800_, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(3u);
v___x_806_ = lean_nat_div(v___x_804_, v___x_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_array_get_size(v_buckets_x27_802_);
v___x_808_ = lean_nat_dec_le(v___x_806_, v___x_807_);
lean_dec(v___x_806_);
if (v___x_808_ == 0)
{
lean_object* v_val_809_; lean_object* v___x_811_; 
v_val_809_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_802_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_val_809_);
lean_ctor_set(v___x_782_, 0, v_size_x27_800_);
v___x_811_ = v___x_782_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_buckets_x27_802_);
lean_ctor_set(v___x_782_, 0, v_size_x27_800_);
v___x_814_ = v___x_782_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_buckets_x27_802_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v___x_816_; lean_object* v_buckets_x27_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_bkt_797_);
v___x_816_ = lean_box(0);
v_buckets_x27_817_ = lean_array_uset(v_buckets_780_, v___x_796_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_777_, v_b_778_, v_bkt_797_);
v___x_819_ = lean_array_uset(v_buckets_x27_817_, v___x_796_, v___x_818_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_819_);
v___x_821_ = v___x_782_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_size_779_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_824_, lean_object* v_e_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = lean_st_ref_take(v_a_824_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_828_, v_e_825_, v_a_826_);
v___x_830_ = lean_st_ref_set(v_a_824_, v___x_829_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_832_, lean_object* v_e_833_, lean_object* v_a_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_832_, v_e_833_, v_a_834_);
lean_dec(v_a_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(lean_object* v_fvars_839_, lean_object* v_pre_840_, lean_object* v_post_841_, uint8_t v_usedLetOnly_842_, uint8_t v_skipConstInApp_843_, uint8_t v_skipInstances_844_, lean_object* v_body_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_array_push(v_fvars_839_, v_x_846_);
v___x_854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_840_, v_post_841_, v_usedLetOnly_842_, v_skipConstInApp_843_, v_skipInstances_844_, v___x_853_, v_body_845_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed(lean_object* v_fvars_855_, lean_object* v_pre_856_, lean_object* v_post_857_, lean_object* v_usedLetOnly_858_, lean_object* v_skipConstInApp_859_, lean_object* v_skipInstances_860_, lean_object* v_body_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v_usedLetOnly_boxed_869_; uint8_t v_skipConstInApp_boxed_870_; uint8_t v_skipInstances_boxed_871_; lean_object* v_res_872_; 
v_usedLetOnly_boxed_869_ = lean_unbox(v_usedLetOnly_858_);
v_skipConstInApp_boxed_870_ = lean_unbox(v_skipConstInApp_859_);
v_skipInstances_boxed_871_ = lean_unbox(v_skipInstances_860_);
v_res_872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0(v_fvars_855_, v_pre_856_, v_post_857_, v_usedLetOnly_boxed_869_, v_skipConstInApp_boxed_870_, v_skipInstances_boxed_871_, v_body_861_, v_x_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(lean_object* v_pre_873_, lean_object* v_post_874_, uint8_t v_usedLetOnly_875_, uint8_t v_skipConstInApp_876_, uint8_t v_skipInstances_877_, lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
lean_inc_ref(v_post_874_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc_ref(v_e_878_);
v___x_885_ = lean_apply_6(v_post_874_, v_e_878_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, lean_box(0));
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_904_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_904_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
switch(lean_obj_tag(v_a_886_))
{
case 0:
{
lean_object* v_e_890_; lean_object* v___x_892_; 
lean_dec_ref(v_e_878_);
lean_dec_ref(v_post_874_);
lean_dec_ref(v_pre_873_);
v_e_890_ = lean_ctor_get(v_a_886_, 0);
lean_inc_ref(v_e_890_);
lean_dec_ref(v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_e_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_e_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
case 1:
{
lean_object* v_e_894_; lean_object* v___x_895_; 
lean_del_object(v___x_888_);
lean_dec_ref(v_e_878_);
v_e_894_ = lean_ctor_get(v_a_886_, 0);
lean_inc_ref(v_e_894_);
lean_dec_ref(v_a_886_);
v___x_895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_873_, v_post_874_, v_usedLetOnly_875_, v_skipConstInApp_876_, v_skipInstances_877_, v_e_894_, v_a_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v___x_895_;
}
default: 
{
lean_object* v_e_x3f_896_; 
lean_dec_ref(v_post_874_);
lean_dec_ref(v_pre_873_);
v_e_x3f_896_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_e_x3f_896_);
lean_dec_ref(v_a_886_);
if (lean_obj_tag(v_e_x3f_896_) == 0)
{
lean_object* v___x_898_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_e_878_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_e_878_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v_val_900_; lean_object* v___x_902_; 
lean_dec_ref(v_e_878_);
v_val_900_ = lean_ctor_get(v_e_x3f_896_, 0);
lean_inc(v_val_900_);
lean_dec_ref(v_e_x3f_896_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_val_900_);
v___x_902_ = v___x_888_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_val_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v_e_878_);
lean_dec_ref(v_post_874_);
lean_dec_ref(v_pre_873_);
v_a_905_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_885_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_885_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(lean_object* v_pre_913_, lean_object* v_post_914_, uint8_t v_usedLetOnly_915_, uint8_t v_skipConstInApp_916_, uint8_t v_skipInstances_917_, lean_object* v_fvars_918_, lean_object* v_e_919_, lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
if (lean_obj_tag(v_e_919_) == 6)
{
lean_object* v_binderName_926_; lean_object* v_binderType_927_; lean_object* v_body_928_; uint8_t v_binderInfo_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_binderName_926_ = lean_ctor_get(v_e_919_, 0);
lean_inc(v_binderName_926_);
v_binderType_927_ = lean_ctor_get(v_e_919_, 1);
lean_inc_ref(v_binderType_927_);
v_body_928_ = lean_ctor_get(v_e_919_, 2);
lean_inc_ref(v_body_928_);
v_binderInfo_929_ = lean_ctor_get_uint8(v_e_919_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_919_);
v___x_930_ = lean_expr_instantiate_rev(v_binderType_927_, v_fvars_918_);
lean_dec_ref(v_binderType_927_);
lean_inc_ref(v_post_914_);
lean_inc_ref(v_pre_913_);
v___x_931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v___x_930_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___f_936_; uint8_t v___x_937_; lean_object* v___x_938_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref(v___x_931_);
v___x_933_ = lean_box(v_usedLetOnly_915_);
v___x_934_ = lean_box(v_skipConstInApp_916_);
v___x_935_ = lean_box(v_skipInstances_917_);
v___f_936_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___lam__0___boxed), 14, 7);
lean_closure_set(v___f_936_, 0, v_fvars_918_);
lean_closure_set(v___f_936_, 1, v_pre_913_);
lean_closure_set(v___f_936_, 2, v_post_914_);
lean_closure_set(v___f_936_, 3, v___x_933_);
lean_closure_set(v___f_936_, 4, v___x_934_);
lean_closure_set(v___f_936_, 5, v___x_935_);
lean_closure_set(v___f_936_, 6, v_body_928_);
v___x_937_ = 0;
v___x_938_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_926_, v_binderInfo_929_, v_a_932_, v___f_936_, v___x_937_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_938_;
}
else
{
lean_dec_ref(v_body_928_);
lean_dec(v_binderName_926_);
lean_dec_ref(v_fvars_918_);
lean_dec_ref(v_post_914_);
lean_dec_ref(v_pre_913_);
return v___x_931_;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_expr_instantiate_rev(v_e_919_, v_fvars_918_);
lean_dec_ref(v_e_919_);
lean_inc_ref(v_post_914_);
lean_inc_ref(v_pre_913_);
v___x_940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v___x_939_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; uint8_t v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref(v___x_940_);
v___x_942_ = 0;
v___x_943_ = 1;
v___x_944_ = 1;
v___x_945_ = l_Lean_Meta_mkLambdaFVars(v_fvars_918_, v_a_941_, v___x_942_, v_usedLetOnly_915_, v___x_942_, v___x_943_, v___x_944_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec_ref(v_fvars_918_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_913_, v_post_914_, v_usedLetOnly_915_, v_skipConstInApp_916_, v_skipInstances_917_, v_a_946_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_947_;
}
else
{
lean_dec_ref(v_post_914_);
lean_dec_ref(v_pre_913_);
return v___x_945_;
}
}
else
{
lean_dec_ref(v_fvars_918_);
lean_dec_ref(v_post_914_);
lean_dec_ref(v_pre_913_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(lean_object* v_fvars_948_, lean_object* v_pre_949_, lean_object* v_post_950_, uint8_t v_usedLetOnly_951_, uint8_t v_skipConstInApp_952_, uint8_t v_skipInstances_953_, lean_object* v_body_954_, lean_object* v_x_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_array_push(v_fvars_948_, v_x_955_);
v___x_963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_949_, v_post_950_, v_usedLetOnly_951_, v_skipConstInApp_952_, v_skipInstances_953_, v___x_962_, v_body_954_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed(lean_object* v_fvars_964_, lean_object* v_pre_965_, lean_object* v_post_966_, lean_object* v_usedLetOnly_967_, lean_object* v_skipConstInApp_968_, lean_object* v_skipInstances_969_, lean_object* v_body_970_, lean_object* v_x_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v_usedLetOnly_boxed_978_; uint8_t v_skipConstInApp_boxed_979_; uint8_t v_skipInstances_boxed_980_; lean_object* v_res_981_; 
v_usedLetOnly_boxed_978_ = lean_unbox(v_usedLetOnly_967_);
v_skipConstInApp_boxed_979_ = lean_unbox(v_skipConstInApp_968_);
v_skipInstances_boxed_980_ = lean_unbox(v_skipInstances_969_);
v_res_981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0(v_fvars_964_, v_pre_965_, v_post_966_, v_usedLetOnly_boxed_978_, v_skipConstInApp_boxed_979_, v_skipInstances_boxed_980_, v_body_970_, v_x_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(lean_object* v_pre_982_, lean_object* v_post_983_, uint8_t v_usedLetOnly_984_, uint8_t v_skipConstInApp_985_, uint8_t v_skipInstances_986_, lean_object* v_fvars_987_, lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
if (lean_obj_tag(v_e_988_) == 8)
{
lean_object* v_declName_995_; lean_object* v_type_996_; lean_object* v_value_997_; lean_object* v_body_998_; uint8_t v_nondep_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_declName_995_ = lean_ctor_get(v_e_988_, 0);
lean_inc(v_declName_995_);
v_type_996_ = lean_ctor_get(v_e_988_, 1);
lean_inc_ref(v_type_996_);
v_value_997_ = lean_ctor_get(v_e_988_, 2);
lean_inc_ref(v_value_997_);
v_body_998_ = lean_ctor_get(v_e_988_, 3);
lean_inc_ref(v_body_998_);
v_nondep_999_ = lean_ctor_get_uint8(v_e_988_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_988_);
v___x_1000_ = lean_expr_instantiate_rev(v_type_996_, v_fvars_987_);
lean_dec_ref(v_type_996_);
lean_inc_ref(v_post_983_);
lean_inc_ref(v_pre_982_);
v___x_1001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_982_, v_post_983_, v_usedLetOnly_984_, v_skipConstInApp_985_, v_skipInstances_986_, v___x_1000_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = lean_expr_instantiate_rev(v_value_997_, v_fvars_987_);
lean_dec_ref(v_value_997_);
lean_inc_ref(v_post_983_);
lean_inc_ref(v_pre_982_);
v___x_1004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_982_, v_post_983_, v_usedLetOnly_984_, v_skipConstInApp_985_, v_skipInstances_986_, v___x_1003_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___f_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_box(v_usedLetOnly_984_);
v___x_1007_ = lean_box(v_skipConstInApp_985_);
v___x_1008_ = lean_box(v_skipInstances_986_);
v___f_1009_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1009_, 0, v_fvars_987_);
lean_closure_set(v___f_1009_, 1, v_pre_982_);
lean_closure_set(v___f_1009_, 2, v_post_983_);
lean_closure_set(v___f_1009_, 3, v___x_1006_);
lean_closure_set(v___f_1009_, 4, v___x_1007_);
lean_closure_set(v___f_1009_, 5, v___x_1008_);
lean_closure_set(v___f_1009_, 6, v_body_998_);
v___x_1010_ = 0;
v___x_1011_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_declName_995_, v_a_1002_, v_a_1005_, v___f_1009_, v_nondep_999_, v___x_1010_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1011_;
}
else
{
lean_dec(v_a_1002_);
lean_dec_ref(v_body_998_);
lean_dec(v_declName_995_);
lean_dec_ref(v_fvars_987_);
lean_dec_ref(v_post_983_);
lean_dec_ref(v_pre_982_);
return v___x_1004_;
}
}
else
{
lean_dec_ref(v_body_998_);
lean_dec_ref(v_value_997_);
lean_dec(v_declName_995_);
lean_dec_ref(v_fvars_987_);
lean_dec_ref(v_post_983_);
lean_dec_ref(v_pre_982_);
return v___x_1001_;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_expr_instantiate_rev(v_e_988_, v_fvars_987_);
lean_dec_ref(v_e_988_);
lean_inc_ref(v_post_983_);
lean_inc_ref(v_pre_982_);
v___x_1013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_982_, v_post_983_, v_usedLetOnly_984_, v_skipConstInApp_985_, v_skipInstances_986_, v___x_1012_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; uint8_t v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = 0;
v___x_1016_ = 1;
v___x_1017_ = l_Lean_Meta_mkLetFVars(v_fvars_987_, v_a_1014_, v_usedLetOnly_984_, v___x_1015_, v___x_1016_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec_ref(v_fvars_987_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_982_, v_post_983_, v_usedLetOnly_984_, v_skipConstInApp_985_, v_skipInstances_986_, v_a_1018_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1019_;
}
else
{
lean_dec_ref(v_post_983_);
lean_dec_ref(v_pre_982_);
return v___x_1017_;
}
}
else
{
lean_dec_ref(v_fvars_987_);
lean_dec_ref(v_post_983_);
lean_dec_ref(v_pre_982_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(lean_object* v_pre_1020_, lean_object* v_post_1021_, uint8_t v_usedLetOnly_1022_, uint8_t v_skipConstInApp_1023_, uint8_t v_skipInstances_1024_, size_t v_sz_1025_, size_t v_i_1026_, lean_object* v_bs_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_lt(v_i_1026_, v_sz_1025_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_post_1021_);
lean_dec_ref(v_pre_1020_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_bs_1027_);
return v___x_1035_;
}
else
{
lean_object* v_v_1036_; lean_object* v___x_1037_; 
v_v_1036_ = lean_array_uget_borrowed(v_bs_1027_, v_i_1026_);
lean_inc(v_v_1036_);
lean_inc_ref(v_post_1021_);
lean_inc_ref(v_pre_1020_);
v___x_1037_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1020_, v_post_1021_, v_usedLetOnly_1022_, v_skipConstInApp_1023_, v_skipInstances_1024_, v_v_1036_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; lean_object* v_bs_x27_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v_bs_x27_1040_ = lean_array_uset(v_bs_1027_, v_i_1026_, v___x_1039_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1026_, v___x_1041_);
v___x_1043_ = lean_array_uset(v_bs_x27_1040_, v_i_1026_, v_a_1038_);
v_i_1026_ = v___x_1042_;
v_bs_1027_ = v___x_1043_;
goto _start;
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_bs_1027_);
lean_dec_ref(v_post_1021_);
lean_dec_ref(v_pre_1020_);
v_a_1045_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1037_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1037_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(lean_object* v_pre_1053_, lean_object* v_post_1054_, uint8_t v_usedLetOnly_1055_, uint8_t v_skipConstInApp_1056_, uint8_t v_skipInstances_1057_, lean_object* v___x_1058_, lean_object* v___y_1059_, lean_object* v_b_1060_, lean_object* v_a_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1053_, v_post_1054_, v_usedLetOnly_1055_, v_skipConstInApp_1056_, v_skipInstances_1057_, v___x_1058_, v___y_1059_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1077_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1077_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1077_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1072_ = lean_array_fset(v_b_1060_, v_a_1061_, v_a_1068_);
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1073_);
v___x_1075_ = v___x_1070_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_b_1060_);
v_a_1078_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1067_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1067_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_pre_1086_, lean_object* v_post_1087_, lean_object* v_usedLetOnly_1088_, lean_object* v_skipConstInApp_1089_, lean_object* v_skipInstances_1090_, lean_object* v___x_1091_, lean_object* v___y_1092_, lean_object* v_b_1093_, lean_object* v_a_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
uint8_t v_usedLetOnly_boxed_1100_; uint8_t v_skipConstInApp_boxed_1101_; uint8_t v_skipInstances_boxed_1102_; lean_object* v_res_1103_; 
v_usedLetOnly_boxed_1100_ = lean_unbox(v_usedLetOnly_1088_);
v_skipConstInApp_boxed_1101_ = lean_unbox(v_skipConstInApp_1089_);
v_skipInstances_boxed_1102_ = lean_unbox(v_skipInstances_1090_);
v_res_1103_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0(v_pre_1086_, v_post_1087_, v_usedLetOnly_boxed_1100_, v_skipConstInApp_boxed_1101_, v_skipInstances_boxed_1102_, v___x_1091_, v___y_1092_, v_b_1093_, v_a_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v_a_1094_);
lean_dec(v___y_1092_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(lean_object* v_upperBound_1104_, lean_object* v___x_1105_, lean_object* v_pre_1106_, lean_object* v_post_1107_, uint8_t v_usedLetOnly_1108_, uint8_t v_skipConstInApp_1109_, uint8_t v_skipInstances_1110_, lean_object* v_a_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___y_1120_; uint8_t v___x_1143_; 
v___x_1143_ = lean_nat_dec_lt(v_a_1111_, v_upperBound_1104_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec(v_a_1111_);
lean_dec_ref(v_post_1107_);
lean_dec_ref(v_pre_1106_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_b_1112_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_array_fget_borrowed(v_b_1112_, v_a_1111_);
v___x_1146_ = lean_array_get_size(v___x_1105_);
v___x_1147_ = lean_nat_dec_lt(v_a_1111_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; 
lean_inc(v___x_1145_);
v___x_1148_ = lean_box(v_usedLetOnly_1108_);
v___x_1149_ = lean_box(v_skipConstInApp_1109_);
v___x_1150_ = lean_box(v_skipInstances_1110_);
lean_inc(v_a_1111_);
lean_inc(v___y_1113_);
lean_inc_ref(v_post_1107_);
lean_inc_ref(v_pre_1106_);
v___f_1151_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1151_, 0, v_pre_1106_);
lean_closure_set(v___f_1151_, 1, v_post_1107_);
lean_closure_set(v___f_1151_, 2, v___x_1148_);
lean_closure_set(v___f_1151_, 3, v___x_1149_);
lean_closure_set(v___f_1151_, 4, v___x_1150_);
lean_closure_set(v___f_1151_, 5, v___x_1145_);
lean_closure_set(v___f_1151_, 6, v___y_1113_);
lean_closure_set(v___f_1151_, 7, v_b_1112_);
lean_closure_set(v___f_1151_, 8, v_a_1111_);
v___y_1120_ = v___f_1151_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1152_; uint8_t v_isInstance_1153_; 
v___x_1152_ = lean_array_fget_borrowed(v___x_1105_, v_a_1111_);
v_isInstance_1153_ = lean_ctor_get_uint8(v___x_1152_, sizeof(void*)*1 + 4);
if (v_isInstance_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; 
lean_inc(v___x_1145_);
v___x_1154_ = lean_box(v_usedLetOnly_1108_);
v___x_1155_ = lean_box(v_skipConstInApp_1109_);
v___x_1156_ = lean_box(v_skipInstances_1110_);
lean_inc(v_a_1111_);
lean_inc(v___y_1113_);
lean_inc_ref(v_post_1107_);
lean_inc_ref(v_pre_1106_);
v___f_1157_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1157_, 0, v_pre_1106_);
lean_closure_set(v___f_1157_, 1, v_post_1107_);
lean_closure_set(v___f_1157_, 2, v___x_1154_);
lean_closure_set(v___f_1157_, 3, v___x_1155_);
lean_closure_set(v___f_1157_, 4, v___x_1156_);
lean_closure_set(v___f_1157_, 5, v___x_1145_);
lean_closure_set(v___f_1157_, 6, v___y_1113_);
lean_closure_set(v___f_1157_, 7, v_b_1112_);
lean_closure_set(v___f_1157_, 8, v_a_1111_);
v___y_1120_ = v___f_1157_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1158_; lean_object* v___f_1159_; 
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_b_1112_);
v___f_1159_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1159_, 0, v___x_1158_);
v___y_1120_ = v___f_1159_;
goto v___jp_1119_;
}
}
}
v___jp_1119_:
{
lean_object* v___x_1121_; 
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
v___x_1121_ = lean_apply_5(v___y_1120_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, lean_box(0));
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1134_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1134_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1134_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; 
lean_dec(v_a_1111_);
lean_dec_ref(v_post_1107_);
lean_dec_ref(v_pre_1106_);
v_a_1126_ = lean_ctor_get(v_a_1122_, 0);
lean_inc(v_a_1126_);
lean_dec_ref(v_a_1122_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_a_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1124_);
v_a_1130_ = lean_ctor_get(v_a_1122_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v_a_1122_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_a_1111_, v___x_1131_);
lean_dec(v_a_1111_);
v_a_1111_ = v___x_1132_;
v_b_1112_ = v_a_1130_;
goto _start;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_a_1111_);
lean_dec_ref(v_post_1107_);
lean_dec_ref(v_pre_1106_);
v_a_1135_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1121_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1121_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(uint8_t v_skipInstances_1160_, lean_object* v_pre_1161_, lean_object* v_post_1162_, uint8_t v_usedLetOnly_1163_, uint8_t v_skipConstInApp_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_f_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; 
if (lean_obj_tag(v_x_1165_) == 5)
{
lean_object* v_fn_1223_; lean_object* v_arg_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_fn_1223_ = lean_ctor_get(v_x_1165_, 0);
lean_inc_ref(v_fn_1223_);
v_arg_1224_ = lean_ctor_get(v_x_1165_, 1);
lean_inc_ref(v_arg_1224_);
lean_dec_ref(v_x_1165_);
v___x_1225_ = lean_array_set(v_x_1166_, v_x_1167_, v_arg_1224_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_sub(v_x_1167_, v___x_1226_);
lean_dec(v_x_1167_);
v_x_1165_ = v_fn_1223_;
v_x_1166_ = v___x_1225_;
v_x_1167_ = v___x_1227_;
goto _start;
}
else
{
lean_dec(v_x_1167_);
if (v_skipConstInApp_1164_ == 0)
{
goto v___jp_1220_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = l_Lean_Expr_isConst(v_x_1165_);
if (v___x_1229_ == 0)
{
goto v___jp_1220_;
}
else
{
v_f_1175_ = v_x_1165_;
v___y_1176_ = v___y_1168_;
v___y_1177_ = v___y_1169_;
v___y_1178_ = v___y_1170_;
v___y_1179_ = v___y_1171_;
v___y_1180_ = v___y_1172_;
goto v___jp_1174_;
}
}
}
v___jp_1174_:
{
if (v_skipInstances_1160_ == 0)
{
size_t v_sz_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v_sz_1181_ = lean_array_size(v_x_1166_);
v___x_1182_ = ((size_t)0ULL);
lean_inc_ref(v_post_1162_);
lean_inc_ref(v_pre_1161_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1161_, v_post_1162_, v_usedLetOnly_1163_, v_skipConstInApp_1164_, v_skipInstances_1160_, v_sz_1181_, v___x_1182_, v_x_1166_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = l_Lean_mkAppN(v_f_1175_, v_a_1184_);
lean_dec(v_a_1184_);
v___x_1186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1161_, v_post_1162_, v_usedLetOnly_1163_, v_skipConstInApp_1164_, v_skipInstances_1160_, v___x_1185_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1186_;
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_f_1175_);
lean_dec_ref(v_post_1162_);
lean_dec_ref(v_pre_1161_);
v_a_1187_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1183_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1183_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_array_get_size(v_x_1166_);
lean_inc_ref(v_f_1175_);
v___x_1196_ = l_Lean_Meta_getFunInfoNArgs(v_f_1175_, v___x_1195_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v_paramInfo_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
v_paramInfo_1198_ = lean_ctor_get(v_a_1197_, 0);
lean_inc_ref(v_paramInfo_1198_);
lean_dec(v_a_1197_);
v___x_1199_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1162_);
lean_inc_ref(v_pre_1161_);
v___x_1200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1195_, v_paramInfo_1198_, v_pre_1161_, v_post_1162_, v_usedLetOnly_1163_, v_skipConstInApp_1164_, v_skipInstances_1160_, v___x_1199_, v_x_1166_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec_ref(v_paramInfo_1198_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = l_Lean_mkAppN(v_f_1175_, v_a_1201_);
lean_dec(v_a_1201_);
v___x_1203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1161_, v_post_1162_, v_usedLetOnly_1163_, v_skipConstInApp_1164_, v_skipInstances_1160_, v___x_1202_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1203_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_f_1175_);
lean_dec_ref(v_post_1162_);
lean_dec_ref(v_pre_1161_);
v_a_1204_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1200_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1200_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_f_1175_);
lean_dec_ref(v_x_1166_);
lean_dec_ref(v_post_1162_);
lean_dec_ref(v_pre_1161_);
v_a_1212_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1196_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1196_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
v___jp_1220_:
{
lean_object* v___x_1221_; 
lean_inc_ref(v_post_1162_);
lean_inc_ref(v_pre_1161_);
v___x_1221_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1161_, v_post_1162_, v_usedLetOnly_1163_, v_skipConstInApp_1164_, v_skipInstances_1160_, v_x_1165_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref(v___x_1221_);
v_f_1175_ = v_a_1222_;
v___y_1176_ = v___y_1168_;
v___y_1177_ = v___y_1169_;
v___y_1178_ = v___y_1170_;
v___y_1179_ = v___y_1171_;
v___y_1180_ = v___y_1172_;
goto v___jp_1174_;
}
else
{
lean_dec_ref(v_x_1166_);
lean_dec_ref(v_post_1162_);
lean_dec_ref(v_pre_1161_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v_pre_1230_, lean_object* v_e_1231_, lean_object* v_post_1232_, uint8_t v_usedLetOnly_1233_, uint8_t v_skipConstInApp_1234_, uint8_t v_skipInstances_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
lean_inc_ref(v_pre_1230_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc_ref(v_e_1231_);
v___x_1242_ = lean_apply_6(v_pre_1230_, v_e_1231_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, lean_box(0));
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
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_e_1231_);
lean_dec_ref(v_pre_1230_);
v_e_1283_ = lean_ctor_get(v_a_1243_, 0);
lean_inc_ref(v_e_1283_);
lean_dec_ref(v_a_1243_);
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
lean_dec_ref(v_e_1231_);
v_e_1287_ = lean_ctor_get(v_a_1243_, 0);
lean_inc_ref(v_e_1287_);
lean_dec_ref(v_a_1243_);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v_e_1287_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1288_;
}
default: 
{
lean_object* v_e_x3f_1289_; 
lean_del_object(v___x_1245_);
v_e_x3f_1289_ = lean_ctor_get(v_a_1243_, 0);
lean_inc(v_e_x3f_1289_);
lean_dec_ref(v_a_1243_);
if (lean_obj_tag(v_e_x3f_1289_) == 0)
{
v___y_1248_ = v_e_1231_;
goto v___jp_1247_;
}
else
{
lean_object* v_val_1290_; 
lean_dec_ref(v_e_1231_);
v_val_1290_ = lean_ctor_get(v_e_x3f_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref(v_e_x3f_1289_);
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
v___x_1250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___x_1249_, v___y_1248_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1250_;
}
case 6:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___x_1251_, v___y_1248_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1252_;
}
case 8:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___x_1253_, v___y_1248_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
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
v___x_1260_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1235_, v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v___y_1248_, v___x_1257_, v___x_1259_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1260_;
}
case 10:
{
lean_object* v_data_1261_; lean_object* v_expr_1262_; lean_object* v___x_1263_; 
v_data_1261_ = lean_ctor_get(v___y_1248_, 0);
v_expr_1262_ = lean_ctor_get(v___y_1248_, 1);
lean_inc_ref(v_expr_1262_);
lean_inc_ref(v_post_1232_);
lean_inc_ref(v_pre_1230_);
v___x_1263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v_expr_1262_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = lean_ptr_addr(v_expr_1262_);
v___x_1266_ = lean_ptr_addr(v_a_1264_);
v___x_1267_ = lean_usize_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_inc(v_data_1261_);
lean_dec_ref(v___y_1248_);
v___x_1268_ = l_Lean_Expr_mdata___override(v_data_1261_, v_a_1264_);
v___x_1269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___x_1268_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_a_1264_);
v___x_1270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___y_1248_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1270_;
}
}
else
{
lean_dec_ref(v___y_1248_);
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1230_);
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
lean_inc_ref(v_post_1232_);
lean_inc_ref(v_pre_1230_);
v___x_1274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v_struct_1273_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; size_t v___x_1276_; size_t v___x_1277_; uint8_t v___x_1278_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = lean_ptr_addr(v_struct_1273_);
v___x_1277_ = lean_ptr_addr(v_a_1275_);
v___x_1278_ = lean_usize_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_inc(v_idx_1272_);
lean_inc(v_typeName_1271_);
lean_dec_ref(v___y_1248_);
v___x_1279_ = l_Lean_Expr_proj___override(v_typeName_1271_, v_idx_1272_, v_a_1275_);
v___x_1280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___x_1279_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_a_1275_);
v___x_1281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___y_1248_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1281_;
}
}
else
{
lean_dec_ref(v___y_1248_);
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1230_);
return v___x_1274_;
}
}
default: 
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1230_, v_post_1232_, v_usedLetOnly_1233_, v_skipConstInApp_1234_, v_skipInstances_1235_, v___y_1248_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_e_1231_);
lean_dec_ref(v_pre_1230_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v_pre_1300_, lean_object* v_e_1301_, lean_object* v_post_1302_, lean_object* v_usedLetOnly_1303_, lean_object* v_skipConstInApp_1304_, lean_object* v_skipInstances_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v_usedLetOnly_boxed_1312_; uint8_t v_skipConstInApp_boxed_1313_; uint8_t v_skipInstances_boxed_1314_; lean_object* v_res_1315_; 
v_usedLetOnly_boxed_1312_ = lean_unbox(v_usedLetOnly_1303_);
v_skipConstInApp_boxed_1313_ = lean_unbox(v_skipConstInApp_1304_);
v_skipInstances_boxed_1314_ = lean_unbox(v_skipInstances_1305_);
v_res_1315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v_pre_1300_, v_e_1301_, v_post_1302_, v_usedLetOnly_boxed_1312_, v_skipConstInApp_boxed_1313_, v_skipInstances_boxed_1314_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1316_, lean_object* v_post_1317_, uint8_t v_usedLetOnly_1318_, uint8_t v_skipConstInApp_1319_, uint8_t v_skipInstances_1320_, lean_object* v_e_1321_, lean_object* v_a_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_inc(v_a_1322_);
v___x_1328_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1328_, 0, lean_box(0));
lean_closure_set(v___x_1328_, 1, lean_box(0));
lean_closure_set(v___x_1328_, 2, v_a_1322_);
v___x_1329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1328_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1363_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1363_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1363_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1330_, v_e_1321_);
lean_dec(v_a_1330_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___f_1338_; lean_object* v___x_1339_; 
lean_del_object(v___x_1332_);
v___x_1335_ = lean_box(v_usedLetOnly_1318_);
v___x_1336_ = lean_box(v_skipConstInApp_1319_);
v___x_1337_ = lean_box(v_skipInstances_1320_);
lean_inc_ref(v_e_1321_);
v___f_1338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1338_, 0, v_pre_1316_);
lean_closure_set(v___f_1338_, 1, v_e_1321_);
lean_closure_set(v___f_1338_, 2, v_post_1317_);
lean_closure_set(v___f_1338_, 3, v___x_1335_);
lean_closure_set(v___f_1338_, 4, v___x_1336_);
lean_closure_set(v___f_1338_, 5, v___x_1337_);
v___x_1339_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1338_, v_a_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_n(v_a_1340_, 2);
lean_dec_ref(v___x_1339_);
lean_inc(v_a_1322_);
v___f_1341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1341_, 0, v_a_1322_);
lean_closure_set(v___f_1341_, 1, v_e_1321_);
lean_closure_set(v___f_1341_, 2, v_a_1340_);
v___x_1342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1341_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v___x_1342_, 0);
lean_dec(v_unused_1350_);
v___x_1344_ = v___x_1342_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v___x_1342_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v_a_1340_);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1340_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_a_1340_);
v_a_1351_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1342_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1342_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_dec_ref(v_e_1321_);
return v___x_1339_;
}
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1361_; 
lean_dec_ref(v_e_1321_);
lean_dec_ref(v_post_1317_);
lean_dec_ref(v_pre_1316_);
v_val_1359_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_val_1359_);
lean_dec_ref(v___x_1334_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_val_1359_);
v___x_1361_ = v___x_1332_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_val_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_e_1321_);
lean_dec_ref(v_post_1317_);
lean_dec_ref(v_pre_1316_);
v_a_1364_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1329_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1329_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1372_, lean_object* v_pre_1373_, lean_object* v_post_1374_, lean_object* v_usedLetOnly_1375_, lean_object* v_skipConstInApp_1376_, lean_object* v_skipInstances_1377_, lean_object* v_body_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_usedLetOnly_boxed_1386_; uint8_t v_skipConstInApp_boxed_1387_; uint8_t v_skipInstances_boxed_1388_; lean_object* v_res_1389_; 
v_usedLetOnly_boxed_1386_ = lean_unbox(v_usedLetOnly_1375_);
v_skipConstInApp_boxed_1387_ = lean_unbox(v_skipConstInApp_1376_);
v_skipInstances_boxed_1388_ = lean_unbox(v_skipInstances_1377_);
v_res_1389_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1372_, v_pre_1373_, v_post_1374_, v_usedLetOnly_boxed_1386_, v_skipConstInApp_boxed_1387_, v_skipInstances_boxed_1388_, v_body_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1390_, lean_object* v_post_1391_, uint8_t v_usedLetOnly_1392_, uint8_t v_skipConstInApp_1393_, uint8_t v_skipInstances_1394_, lean_object* v_fvars_1395_, lean_object* v_e_1396_, lean_object* v_a_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
if (lean_obj_tag(v_e_1396_) == 7)
{
lean_object* v_binderName_1403_; lean_object* v_binderType_1404_; lean_object* v_body_1405_; uint8_t v_binderInfo_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_binderName_1403_ = lean_ctor_get(v_e_1396_, 0);
lean_inc(v_binderName_1403_);
v_binderType_1404_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_binderType_1404_);
v_body_1405_ = lean_ctor_get(v_e_1396_, 2);
lean_inc_ref(v_body_1405_);
v_binderInfo_1406_ = lean_ctor_get_uint8(v_e_1396_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1396_);
v___x_1407_ = lean_expr_instantiate_rev(v_binderType_1404_, v_fvars_1395_);
lean_dec_ref(v_binderType_1404_);
lean_inc_ref(v_post_1391_);
lean_inc_ref(v_pre_1390_);
v___x_1408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1390_, v_post_1391_, v_usedLetOnly_1392_, v_skipConstInApp_1393_, v_skipInstances_1394_, v___x_1407_, v_a_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = lean_box(v_usedLetOnly_1392_);
v___x_1411_ = lean_box(v_skipConstInApp_1393_);
v___x_1412_ = lean_box(v_skipInstances_1394_);
v___f_1413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1413_, 0, v_fvars_1395_);
lean_closure_set(v___f_1413_, 1, v_pre_1390_);
lean_closure_set(v___f_1413_, 2, v_post_1391_);
lean_closure_set(v___f_1413_, 3, v___x_1410_);
lean_closure_set(v___f_1413_, 4, v___x_1411_);
lean_closure_set(v___f_1413_, 5, v___x_1412_);
lean_closure_set(v___f_1413_, 6, v_body_1405_);
v___x_1414_ = 0;
v___x_1415_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1403_, v_binderInfo_1406_, v_a_1409_, v___f_1413_, v___x_1414_, v_a_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1415_;
}
else
{
lean_dec_ref(v_body_1405_);
lean_dec(v_binderName_1403_);
lean_dec_ref(v_fvars_1395_);
lean_dec_ref(v_post_1391_);
lean_dec_ref(v_pre_1390_);
return v___x_1408_;
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_expr_instantiate_rev(v_e_1396_, v_fvars_1395_);
lean_dec_ref(v_e_1396_);
lean_inc_ref(v_post_1391_);
lean_inc_ref(v_pre_1390_);
v___x_1417_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1390_, v_post_1391_, v_usedLetOnly_1392_, v_skipConstInApp_1393_, v_skipInstances_1394_, v___x_1416_, v_a_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; uint8_t v___x_1419_; uint8_t v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = 0;
v___x_1420_ = 1;
v___x_1421_ = 1;
v___x_1422_ = l_Lean_Meta_mkForallFVars(v_fvars_1395_, v_a_1418_, v___x_1419_, v_usedLetOnly_1392_, v___x_1420_, v___x_1421_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec_ref(v_fvars_1395_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1390_, v_post_1391_, v_usedLetOnly_1392_, v_skipConstInApp_1393_, v_skipInstances_1394_, v_a_1423_, v_a_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1424_;
}
else
{
lean_dec_ref(v_post_1391_);
lean_dec_ref(v_pre_1390_);
return v___x_1422_;
}
}
else
{
lean_dec_ref(v_fvars_1395_);
lean_dec_ref(v_post_1391_);
lean_dec_ref(v_pre_1390_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1425_, lean_object* v_pre_1426_, lean_object* v_post_1427_, uint8_t v_usedLetOnly_1428_, uint8_t v_skipConstInApp_1429_, uint8_t v_skipInstances_1430_, lean_object* v_body_1431_, lean_object* v_x_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_array_push(v_fvars_1425_, v_x_1432_);
v___x_1440_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1426_, v_post_1427_, v_usedLetOnly_1428_, v_skipConstInApp_1429_, v_skipInstances_1430_, v___x_1439_, v_body_1431_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1441_, lean_object* v_post_1442_, lean_object* v_usedLetOnly_1443_, lean_object* v_skipConstInApp_1444_, lean_object* v_skipInstances_1445_, lean_object* v_e_1446_, lean_object* v_a_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v_usedLetOnly_boxed_1453_; uint8_t v_skipConstInApp_boxed_1454_; uint8_t v_skipInstances_boxed_1455_; lean_object* v_res_1456_; 
v_usedLetOnly_boxed_1453_ = lean_unbox(v_usedLetOnly_1443_);
v_skipConstInApp_boxed_1454_ = lean_unbox(v_skipConstInApp_1444_);
v_skipInstances_boxed_1455_ = lean_unbox(v_skipInstances_1445_);
v_res_1456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1441_, v_post_1442_, v_usedLetOnly_boxed_1453_, v_skipConstInApp_boxed_1454_, v_skipInstances_boxed_1455_, v_e_1446_, v_a_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v_a_1447_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1457_, lean_object* v_post_1458_, lean_object* v_usedLetOnly_1459_, lean_object* v_skipConstInApp_1460_, lean_object* v_skipInstances_1461_, lean_object* v_sz_1462_, lean_object* v_i_1463_, lean_object* v_bs_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_usedLetOnly_boxed_1471_; uint8_t v_skipConstInApp_boxed_1472_; uint8_t v_skipInstances_boxed_1473_; size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_usedLetOnly_boxed_1471_ = lean_unbox(v_usedLetOnly_1459_);
v_skipConstInApp_boxed_1472_ = lean_unbox(v_skipConstInApp_1460_);
v_skipInstances_boxed_1473_ = lean_unbox(v_skipInstances_1461_);
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1462_);
lean_dec(v_sz_1462_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1463_);
lean_dec(v_i_1463_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1457_, v_post_1458_, v_usedLetOnly_boxed_1471_, v_skipConstInApp_boxed_1472_, v_skipInstances_boxed_1473_, v_sz_boxed_1474_, v_i_boxed_1475_, v_bs_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1477_, lean_object* v_post_1478_, lean_object* v_usedLetOnly_1479_, lean_object* v_skipConstInApp_1480_, lean_object* v_skipInstances_1481_, lean_object* v_e_1482_, lean_object* v_a_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v_usedLetOnly_boxed_1489_; uint8_t v_skipConstInApp_boxed_1490_; uint8_t v_skipInstances_boxed_1491_; lean_object* v_res_1492_; 
v_usedLetOnly_boxed_1489_ = lean_unbox(v_usedLetOnly_1479_);
v_skipConstInApp_boxed_1490_ = lean_unbox(v_skipConstInApp_1480_);
v_skipInstances_boxed_1491_ = lean_unbox(v_skipInstances_1481_);
v_res_1492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1477_, v_post_1478_, v_usedLetOnly_boxed_1489_, v_skipConstInApp_boxed_1490_, v_skipInstances_boxed_1491_, v_e_1482_, v_a_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v_a_1483_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1493_, lean_object* v_post_1494_, lean_object* v_usedLetOnly_1495_, lean_object* v_skipConstInApp_1496_, lean_object* v_skipInstances_1497_, lean_object* v_fvars_1498_, lean_object* v_e_1499_, lean_object* v_a_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v_usedLetOnly_boxed_1506_; uint8_t v_skipConstInApp_boxed_1507_; uint8_t v_skipInstances_boxed_1508_; lean_object* v_res_1509_; 
v_usedLetOnly_boxed_1506_ = lean_unbox(v_usedLetOnly_1495_);
v_skipConstInApp_boxed_1507_ = lean_unbox(v_skipConstInApp_1496_);
v_skipInstances_boxed_1508_ = lean_unbox(v_skipInstances_1497_);
v_res_1509_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1493_, v_post_1494_, v_usedLetOnly_boxed_1506_, v_skipConstInApp_boxed_1507_, v_skipInstances_boxed_1508_, v_fvars_1498_, v_e_1499_, v_a_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_a_1500_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1510_, lean_object* v_post_1511_, lean_object* v_usedLetOnly_1512_, lean_object* v_skipConstInApp_1513_, lean_object* v_skipInstances_1514_, lean_object* v_fvars_1515_, lean_object* v_e_1516_, lean_object* v_a_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_usedLetOnly_boxed_1523_; uint8_t v_skipConstInApp_boxed_1524_; uint8_t v_skipInstances_boxed_1525_; lean_object* v_res_1526_; 
v_usedLetOnly_boxed_1523_ = lean_unbox(v_usedLetOnly_1512_);
v_skipConstInApp_boxed_1524_ = lean_unbox(v_skipConstInApp_1513_);
v_skipInstances_boxed_1525_ = lean_unbox(v_skipInstances_1514_);
v_res_1526_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1510_, v_post_1511_, v_usedLetOnly_boxed_1523_, v_skipConstInApp_boxed_1524_, v_skipInstances_boxed_1525_, v_fvars_1515_, v_e_1516_, v_a_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v_a_1517_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1527_, lean_object* v_post_1528_, lean_object* v_usedLetOnly_1529_, lean_object* v_skipConstInApp_1530_, lean_object* v_skipInstances_1531_, lean_object* v_fvars_1532_, lean_object* v_e_1533_, lean_object* v_a_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v_usedLetOnly_boxed_1540_; uint8_t v_skipConstInApp_boxed_1541_; uint8_t v_skipInstances_boxed_1542_; lean_object* v_res_1543_; 
v_usedLetOnly_boxed_1540_ = lean_unbox(v_usedLetOnly_1529_);
v_skipConstInApp_boxed_1541_ = lean_unbox(v_skipConstInApp_1530_);
v_skipInstances_boxed_1542_ = lean_unbox(v_skipInstances_1531_);
v_res_1543_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1527_, v_post_1528_, v_usedLetOnly_boxed_1540_, v_skipConstInApp_boxed_1541_, v_skipInstances_boxed_1542_, v_fvars_1532_, v_e_1533_, v_a_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_a_1534_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1544_, lean_object* v___x_1545_, lean_object* v_pre_1546_, lean_object* v_post_1547_, lean_object* v_usedLetOnly_1548_, lean_object* v_skipConstInApp_1549_, lean_object* v_skipInstances_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v_usedLetOnly_boxed_1559_; uint8_t v_skipConstInApp_boxed_1560_; uint8_t v_skipInstances_boxed_1561_; lean_object* v_res_1562_; 
v_usedLetOnly_boxed_1559_ = lean_unbox(v_usedLetOnly_1548_);
v_skipConstInApp_boxed_1560_ = lean_unbox(v_skipConstInApp_1549_);
v_skipInstances_boxed_1561_ = lean_unbox(v_skipInstances_1550_);
v_res_1562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1544_, v___x_1545_, v_pre_1546_, v_post_1547_, v_usedLetOnly_boxed_1559_, v_skipConstInApp_boxed_1560_, v_skipInstances_boxed_1561_, v_a_1551_, v_b_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___x_1545_);
lean_dec(v_upperBound_1544_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1563_, lean_object* v_pre_1564_, lean_object* v_post_1565_, lean_object* v_usedLetOnly_1566_, lean_object* v_skipConstInApp_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_skipInstances_boxed_1577_; uint8_t v_usedLetOnly_boxed_1578_; uint8_t v_skipConstInApp_boxed_1579_; lean_object* v_res_1580_; 
v_skipInstances_boxed_1577_ = lean_unbox(v_skipInstances_1563_);
v_usedLetOnly_boxed_1578_ = lean_unbox(v_usedLetOnly_1566_);
v_skipConstInApp_boxed_1579_ = lean_unbox(v_skipConstInApp_1567_);
v_res_1580_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1577_, v_pre_1564_, v_post_1565_, v_usedLetOnly_boxed_1578_, v_skipConstInApp_boxed_1579_, v_x_1568_, v_x_1569_, v_x_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
return v_res_1580_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_unsigned_to_nat(16u);
v___x_1583_ = lean_mk_array(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v___x_1584_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1588_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1588_, 0, lean_box(0));
lean_closure_set(v___x_1588_, 1, lean_box(0));
lean_closure_set(v___x_1588_, 2, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1589_, lean_object* v_pre_1590_, lean_object* v_post_1591_, uint8_t v_usedLetOnly_1592_, uint8_t v_skipConstInApp_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_a_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1599_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1600_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1599_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = 0;
v___x_1603_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1590_, v_post_1591_, v_usedLetOnly_1592_, v_skipConstInApp_1593_, v___x_1602_, v_input_1589_, v_a_1601_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1605_, 0, lean_box(0));
lean_closure_set(v___x_1605_, 1, lean_box(0));
lean_closure_set(v___x_1605_, 2, v_a_1601_);
v___x_1606_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1605_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1614_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_a_1604_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1604_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_dec(v_a_1601_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1615_, lean_object* v_pre_1616_, lean_object* v_post_1617_, lean_object* v_usedLetOnly_1618_, lean_object* v_skipConstInApp_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
uint8_t v_usedLetOnly_boxed_1625_; uint8_t v_skipConstInApp_boxed_1626_; lean_object* v_res_1627_; 
v_usedLetOnly_boxed_1625_ = lean_unbox(v_usedLetOnly_1618_);
v_skipConstInApp_boxed_1626_ = lean_unbox(v_skipConstInApp_1619_);
v_res_1627_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1615_, v_pre_1616_, v_post_1617_, v_usedLetOnly_boxed_1625_, v_skipConstInApp_boxed_1626_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1627_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__2(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__1));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__4(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__3));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1635_, lean_object* v_argsPacker_1636_, lean_object* v_funNames_1637_, lean_object* v_newF_1638_, lean_object* v_e_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1645_; 
lean_inc(v_a_1643_);
lean_inc_ref(v_a_1642_);
lean_inc(v_a_1641_);
lean_inc_ref(v_a_1640_);
lean_inc_ref(v_newF_1638_);
v___x_1645_ = lean_infer_type(v_newF_1638_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___f_1647_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___x_1658_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___f_1647_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1658_ = l_Lean_Expr_isForall(v_a_1646_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref(v_e_1639_);
lean_dec_ref(v_funNames_1637_);
lean_dec_ref(v_argsPacker_1636_);
lean_dec_ref(v_fixedParamPerms_1635_);
v___x_1659_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__2, &l_Lean_Elab_WF_packCalls___closed__2_once, _init_l_Lean_Elab_WF_packCalls___closed__2);
v___x_1660_ = l_Lean_MessageData_ofExpr(v_newF_1638_);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1659_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__4, &l_Lean_Elab_WF_packCalls___closed__4_once, _init_l_Lean_Elab_WF_packCalls___closed__4);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_MessageData_ofExpr(v_a_1646_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1665_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
v___y_1649_ = v_a_1640_;
v___y_1650_ = v_a_1641_;
v___y_1651_ = v_a_1642_;
v___y_1652_ = v_a_1643_;
goto v___jp_1648_;
}
v___jp_1648_:
{
lean_object* v___x_1653_; lean_object* v___f_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1653_ = l_Lean_Expr_bindingDomain_x21(v_a_1646_);
lean_dec(v_a_1646_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1654_, 0, v_funNames_1637_);
lean_closure_set(v___f_1654_, 1, v_fixedParamPerms_1635_);
lean_closure_set(v___f_1654_, 2, v_argsPacker_1636_);
lean_closure_set(v___f_1654_, 3, v___x_1653_);
lean_closure_set(v___f_1654_, 4, v_newF_1638_);
v___x_1655_ = 0;
v___x_1656_ = 1;
v___x_1657_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1639_, v___f_1647_, v___f_1654_, v___x_1655_, v___x_1656_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1657_;
}
}
else
{
lean_dec_ref(v_e_1639_);
lean_dec_ref(v_newF_1638_);
lean_dec_ref(v_funNames_1637_);
lean_dec_ref(v_argsPacker_1636_);
lean_dec_ref(v_fixedParamPerms_1635_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1675_, lean_object* v_argsPacker_1676_, lean_object* v_funNames_1677_, lean_object* v_newF_1678_, lean_object* v_e_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1675_, v_argsPacker_1676_, v_funNames_1677_, v_newF_1678_, v_e_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1686_, lean_object* v___x_1687_, lean_object* v_pre_1688_, lean_object* v_post_1689_, uint8_t v_usedLetOnly_1690_, uint8_t v_skipConstInApp_1691_, uint8_t v_skipInstances_1692_, lean_object* v___x_1693_, lean_object* v_inst_1694_, lean_object* v_R_1695_, lean_object* v_a_1696_, lean_object* v_b_1697_, lean_object* v_c_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1686_, v___x_1687_, v_pre_1688_, v_post_1689_, v_usedLetOnly_1690_, v_skipConstInApp_1691_, v_skipInstances_1692_, v_a_1696_, v_b_1697_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1706_ = _args[0];
lean_object* v___x_1707_ = _args[1];
lean_object* v_pre_1708_ = _args[2];
lean_object* v_post_1709_ = _args[3];
lean_object* v_usedLetOnly_1710_ = _args[4];
lean_object* v_skipConstInApp_1711_ = _args[5];
lean_object* v_skipInstances_1712_ = _args[6];
lean_object* v___x_1713_ = _args[7];
lean_object* v_inst_1714_ = _args[8];
lean_object* v_R_1715_ = _args[9];
lean_object* v_a_1716_ = _args[10];
lean_object* v_b_1717_ = _args[11];
lean_object* v_c_1718_ = _args[12];
lean_object* v___y_1719_ = _args[13];
lean_object* v___y_1720_ = _args[14];
lean_object* v___y_1721_ = _args[15];
lean_object* v___y_1722_ = _args[16];
lean_object* v___y_1723_ = _args[17];
lean_object* v___y_1724_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1725_; uint8_t v_skipConstInApp_boxed_1726_; uint8_t v_skipInstances_boxed_1727_; lean_object* v_res_1728_; 
v_usedLetOnly_boxed_1725_ = lean_unbox(v_usedLetOnly_1710_);
v_skipConstInApp_boxed_1726_ = lean_unbox(v_skipConstInApp_1711_);
v_skipInstances_boxed_1727_ = lean_unbox(v_skipInstances_1712_);
v_res_1728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1706_, v___x_1707_, v_pre_1708_, v_post_1709_, v_usedLetOnly_boxed_1725_, v_skipConstInApp_boxed_1726_, v_skipInstances_boxed_1727_, v___x_1713_, v_inst_1714_, v_R_1715_, v_a_1716_, v_b_1717_, v_c_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v___x_1713_);
lean_dec_ref(v___x_1707_);
lean_dec(v_upperBound_1706_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1729_, lean_object* v_m_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1730_, v_a_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1733_, lean_object* v_m_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1733_, v_m_1734_, v_a_1735_);
lean_dec_ref(v_a_1735_);
lean_dec_ref(v_m_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1737_, lean_object* v_name_1738_, uint8_t v_bi_1739_, lean_object* v_type_1740_, lean_object* v_k_1741_, uint8_t v_kind_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1738_, v_bi_1739_, v_type_1740_, v_k_1741_, v_kind_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_name_1751_, lean_object* v_bi_1752_, lean_object* v_type_1753_, lean_object* v_k_1754_, lean_object* v_kind_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v_bi_boxed_1762_; uint8_t v_kind_boxed_1763_; lean_object* v_res_1764_; 
v_bi_boxed_1762_ = lean_unbox(v_bi_1752_);
v_kind_boxed_1763_ = lean_unbox(v_kind_1755_);
v_res_1764_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1750_, v_name_1751_, v_bi_boxed_1762_, v_type_1753_, v_k_1754_, v_kind_boxed_1763_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1765_, lean_object* v_name_1766_, lean_object* v_type_1767_, lean_object* v_val_1768_, lean_object* v_k_1769_, uint8_t v_nondep_1770_, uint8_t v_kind_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1766_, v_type_1767_, v_val_1768_, v_k_1769_, v_nondep_1770_, v_kind_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_name_1780_, lean_object* v_type_1781_, lean_object* v_val_1782_, lean_object* v_k_1783_, lean_object* v_nondep_1784_, lean_object* v_kind_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v_nondep_boxed_1792_; uint8_t v_kind_boxed_1793_; lean_object* v_res_1794_; 
v_nondep_boxed_1792_ = lean_unbox(v_nondep_1784_);
v_kind_boxed_1793_ = lean_unbox(v_kind_1785_);
v_res_1794_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1779_, v_name_1780_, v_type_1781_, v_val_1782_, v_k_1783_, v_nondep_boxed_1792_, v_kind_boxed_1793_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1795_, lean_object* v_ref_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1796_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_ref_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1803_, v_ref_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1820_, v_x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1829_, lean_object* v_m_1830_, lean_object* v_a_1831_, lean_object* v_b_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1830_, v_a_1831_, v_b_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1834_, lean_object* v_a_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1838_, v_a_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1842_, lean_object* v_a_1843_, lean_object* v_x_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1843_, v_x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1846_, lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1846_, v_a_1847_, v_x_1848_);
lean_dec(v_x_1848_);
lean_dec_ref(v_a_1847_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1851_, lean_object* v_data_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1854_, lean_object* v_a_1855_, lean_object* v_b_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1855_, v_b_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1859_, lean_object* v_i_1860_, lean_object* v_source_1861_, lean_object* v_target_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1860_, v_source_1861_, v_target_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1865_, v_x_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1874_, lean_object* v_argsPacker_1875_, lean_object* v_preDefs_1876_){
_start:
{
uint8_t v___y_1878_; uint8_t v___x_1898_; 
v___x_1898_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1874_);
if (v___x_1898_ == 0)
{
v___y_1878_ = v___x_1898_;
goto v___jp_1877_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1875_);
v___y_1878_ = v___x_1899_;
goto v___jp_1877_;
}
v___jp_1877_:
{
if (v___y_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1879_ = lean_unsigned_to_nat(1u);
v___x_1880_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1875_);
v___x_1881_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
lean_dec(v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_declName_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1882_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_array_get_borrowed(v___x_1882_, v_preDefs_1876_, v___x_1883_);
v_declName_1885_ = lean_ctor_get(v___x_1884_, 3);
v___x_1886_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1885_);
v___x_1887_ = l_Lean_Name_append(v_declName_1885_, v___x_1886_);
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_declName_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1888_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_array_get_borrowed(v___x_1888_, v_preDefs_1876_, v___x_1889_);
v_declName_1891_ = lean_ctor_get(v___x_1890_, 3);
v___x_1892_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1891_);
v___x_1893_ = l_Lean_Name_append(v_declName_1891_, v___x_1892_);
return v___x_1893_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_declName_1897_; 
v___x_1894_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_array_get_borrowed(v___x_1894_, v_preDefs_1876_, v___x_1895_);
v_declName_1897_ = lean_ctor_get(v___x_1896_, 3);
lean_inc(v_declName_1897_);
return v_declName_1897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1900_, lean_object* v_argsPacker_1901_, lean_object* v_preDefs_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1900_, v_argsPacker_1901_, v_preDefs_1902_);
lean_dec_ref(v_preDefs_1902_);
lean_dec_ref(v_argsPacker_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
v___x_1911_ = lean_apply_6(v_k_1904_, v_b_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, lean_box(0));
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1912_, v_b_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1920_, lean_object* v_type_1921_, lean_object* v_k_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___f_1928_; lean_object* v___x_1929_; 
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1928_, 0, v_k_1922_);
v___x_1929_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1920_, v_type_1921_, v___f_1928_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1938_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1929_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1929_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1946_, lean_object* v_type_1947_, lean_object* v_k_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1946_, v_type_1947_, v_k_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1955_, lean_object* v_perm_1956_, lean_object* v_type_1957_, lean_object* v_k_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1956_, v_type_1957_, v_k_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_perm_1966_, lean_object* v_type_1967_, lean_object* v_k_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1965_, v_perm_1966_, v_type_1967_, v_k_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1975_, lean_object* v_ys_1976_, lean_object* v_as_1977_, lean_object* v_i_1978_, lean_object* v_j_1979_, lean_object* v_bs_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_zero_1986_; uint8_t v_isZero_1987_; 
v_zero_1986_ = lean_unsigned_to_nat(0u);
v_isZero_1987_ = lean_nat_dec_eq(v_i_1978_, v_zero_1986_);
if (v_isZero_1987_ == 1)
{
lean_object* v___x_1988_; 
lean_dec(v_j_1979_);
lean_dec(v_i_1978_);
lean_dec_ref(v_ys_1976_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_bs_1980_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; lean_object* v_value_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1989_ = lean_array_fget_borrowed(v_as_1977_, v_j_1979_);
v_value_1990_ = lean_ctor_get(v___x_1989_, 7);
v___x_1991_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_1992_ = lean_array_get_borrowed(v___x_1991_, v___x_1975_, v_j_1979_);
lean_inc_ref(v_ys_1976_);
lean_inc_ref(v_value_1990_);
lean_inc(v___x_1992_);
v___x_1993_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1992_, v_value_1990_, v_ys_1976_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v_one_1995_; lean_object* v_n_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref(v___x_1993_);
v_one_1995_ = lean_unsigned_to_nat(1u);
v_n_1996_ = lean_nat_sub(v_i_1978_, v_one_1995_);
lean_dec(v_i_1978_);
v___x_1997_ = lean_nat_add(v_j_1979_, v_one_1995_);
lean_dec(v_j_1979_);
v___x_1998_ = lean_array_push(v_bs_1980_, v_a_1994_);
v_i_1978_ = v_n_1996_;
v_j_1979_ = v___x_1997_;
v_bs_1980_ = v___x_1998_;
goto _start;
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_bs_1980_);
lean_dec(v_j_1979_);
lean_dec(v_i_1978_);
lean_dec_ref(v_ys_1976_);
v_a_2000_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1993_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1993_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2008_, lean_object* v_ys_2009_, lean_object* v_as_2010_, lean_object* v_i_2011_, lean_object* v_j_2012_, lean_object* v_bs_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2008_, v_ys_2009_, v_as_2010_, v_i_2011_, v_j_2012_, v_bs_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v_as_2010_);
lean_dec_ref(v___x_2008_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2020_, lean_object* v_ys_2021_, lean_object* v_as_2022_, lean_object* v_i_2023_, lean_object* v_j_2024_, lean_object* v_bs_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_zero_2031_; uint8_t v_isZero_2032_; 
v_zero_2031_ = lean_unsigned_to_nat(0u);
v_isZero_2032_ = lean_nat_dec_eq(v_i_2023_, v_zero_2031_);
if (v_isZero_2032_ == 1)
{
lean_object* v___x_2033_; 
lean_dec(v_j_2024_);
lean_dec(v_i_2023_);
lean_dec_ref(v_ys_2021_);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_bs_2025_);
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v_type_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2034_ = lean_array_fget_borrowed(v_as_2022_, v_j_2024_);
v_type_2035_ = lean_ctor_get(v___x_2034_, 6);
v___x_2036_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2037_ = lean_array_get_borrowed(v___x_2036_, v___x_2020_, v_j_2024_);
lean_inc_ref(v_ys_2021_);
lean_inc_ref(v_type_2035_);
lean_inc(v___x_2037_);
v___x_2038_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2037_, v_type_2035_, v_ys_2021_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_one_2040_; lean_object* v_n_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2038_);
v_one_2040_ = lean_unsigned_to_nat(1u);
v_n_2041_ = lean_nat_sub(v_i_2023_, v_one_2040_);
lean_dec(v_i_2023_);
v___x_2042_ = lean_nat_add(v_j_2024_, v_one_2040_);
lean_dec(v_j_2024_);
v___x_2043_ = lean_array_push(v_bs_2025_, v_a_2039_);
v_i_2023_ = v_n_2041_;
v_j_2024_ = v___x_2042_;
v_bs_2025_ = v___x_2043_;
goto _start;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_bs_2025_);
lean_dec(v_j_2024_);
lean_dec(v_i_2023_);
lean_dec_ref(v_ys_2021_);
v_a_2045_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2038_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2038_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2053_, lean_object* v_ys_2054_, lean_object* v_as_2055_, lean_object* v_i_2056_, lean_object* v_j_2057_, lean_object* v_bs_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2053_, v_ys_2054_, v_as_2055_, v_i_2056_, v_j_2057_, v_bs_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec_ref(v_as_2055_);
lean_dec_ref(v___x_2053_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
if (lean_obj_tag(v_a_2065_) == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_List_reverse___redArg(v_a_2066_);
return v___x_2067_;
}
else
{
lean_object* v_head_2068_; lean_object* v_tail_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2078_; 
v_head_2068_ = lean_ctor_get(v_a_2065_, 0);
v_tail_2069_ = lean_ctor_get(v_a_2065_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2065_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2071_ = v_a_2065_;
v_isShared_2072_ = v_isSharedCheck_2078_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_tail_2069_);
lean_inc(v_head_2068_);
lean_dec(v_a_2065_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2078_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = l_Lean_mkLevelParam(v_head_2068_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2066_);
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_a_2066_);
v___x_2075_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
v_a_2065_ = v_tail_2069_;
v_a_2066_ = v___x_2075_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_bs_2081_){
_start:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2082_ == 0)
{
return v_bs_2081_;
}
else
{
lean_object* v_v_2083_; lean_object* v_declName_2084_; lean_object* v___x_2085_; lean_object* v_bs_x27_2086_; size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v_v_2083_ = lean_array_uget_borrowed(v_bs_2081_, v_i_2080_);
v_declName_2084_ = lean_ctor_get(v_v_2083_, 3);
lean_inc(v_declName_2084_);
v___x_2085_ = lean_unsigned_to_nat(0u);
v_bs_x27_2086_ = lean_array_uset(v_bs_2081_, v_i_2080_, v___x_2085_);
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2080_, v___x_2087_);
v___x_2089_ = lean_array_uset(v_bs_x27_2086_, v_i_2080_, v_declName_2084_);
v_i_2080_ = v___x_2088_;
v_bs_2081_ = v___x_2089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2091_, lean_object* v_i_2092_, lean_object* v_bs_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2091_);
lean_dec(v_sz_2091_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2097_, lean_object* v_perms_2098_, lean_object* v___x_2099_, lean_object* v_argsPacker_2100_, uint8_t v___x_2101_, lean_object* v_ref_2102_, uint8_t v_kind_2103_, lean_object* v_levelParams_2104_, lean_object* v_modifiers_2105_, lean_object* v_newFn_2106_, lean_object* v_binders_2107_, lean_object* v_numSectionVars_2108_, lean_object* v_value_2109_, lean_object* v_termination_2110_, lean_object* v_fixedParamPerms_2111_, lean_object* v_ys_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_array_get_size(v_preDefs_2097_);
v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2118_);
lean_inc_ref(v___x_2119_);
lean_inc(v___x_2099_);
lean_inc_ref(v_ys_2112_);
v___x_2120_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2098_, v_ys_2112_, v_preDefs_2097_, v___x_2118_, v___x_2099_, v___x_2119_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
lean_inc_ref(v_ys_2112_);
v___x_2122_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2098_, v_ys_2112_, v_preDefs_2097_, v___x_2118_, v___x_2099_, v___x_2119_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2100_, v_a_2121_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; uint8_t v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = 1;
v___x_2127_ = 1;
v___x_2128_ = l_Lean_Meta_mkForallFVars(v_ys_2112_, v_a_2125_, v___x_2101_, v___x_2126_, v___x_2126_, v___x_2127_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_n(v_a_2129_, 2);
lean_dec_ref(v___x_2128_);
lean_inc_ref(v_termination_2110_);
lean_inc(v_numSectionVars_2108_);
lean_inc(v_binders_2107_);
lean_inc(v_newFn_2106_);
lean_inc_ref(v_modifiers_2105_);
lean_inc(v_levelParams_2104_);
lean_inc(v_ref_2102_);
v___x_2130_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2130_, 0, v_ref_2102_);
lean_ctor_set(v___x_2130_, 1, v_levelParams_2104_);
lean_ctor_set(v___x_2130_, 2, v_modifiers_2105_);
lean_ctor_set(v___x_2130_, 3, v_newFn_2106_);
lean_ctor_set(v___x_2130_, 4, v_binders_2107_);
lean_ctor_set(v___x_2130_, 5, v_numSectionVars_2108_);
lean_ctor_set(v___x_2130_, 6, v_a_2129_);
lean_ctor_set(v___x_2130_, 7, v_value_2109_);
lean_ctor_set(v___x_2130_, 8, v_termination_2110_);
lean_ctor_set_uint8(v___x_2130_, sizeof(void*)*9, v_kind_2103_);
v___x_2131_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2130_, v___y_2115_, v___y_2116_);
lean_dec_ref(v___x_2130_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2132_; 
lean_dec_ref(v___x_2131_);
v___x_2132_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2100_, v_a_2123_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v_a_2123_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; size_t v_sz_2138_; size_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = lean_box(0);
lean_inc(v_levelParams_2104_);
v___x_2135_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2104_, v___x_2134_);
lean_inc(v_newFn_2106_);
v___x_2136_ = l_Lean_mkConst(v_newFn_2106_, v___x_2135_);
v___x_2137_ = l_Lean_mkAppN(v___x_2136_, v_ys_2112_);
v_sz_2138_ = lean_array_size(v_preDefs_2097_);
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2138_, v___x_2139_, v_preDefs_2097_);
v___x_2141_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2111_, v_argsPacker_2100_, v___x_2140_, v___x_2137_, v_a_2133_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = l_Lean_Meta_mkLambdaFVars(v_ys_2112_, v_a_2142_, v___x_2101_, v___x_2126_, v___x_2101_, v___x_2126_, v___x_2127_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec_ref(v_ys_2112_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2152_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2148_, 0, v_ref_2102_);
lean_ctor_set(v___x_2148_, 1, v_levelParams_2104_);
lean_ctor_set(v___x_2148_, 2, v_modifiers_2105_);
lean_ctor_set(v___x_2148_, 3, v_newFn_2106_);
lean_ctor_set(v___x_2148_, 4, v_binders_2107_);
lean_ctor_set(v___x_2148_, 5, v_numSectionVars_2108_);
lean_ctor_set(v___x_2148_, 6, v_a_2129_);
lean_ctor_set(v___x_2148_, 7, v_a_2144_);
lean_ctor_set(v___x_2148_, 8, v_termination_2110_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*9, v_kind_2103_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_a_2129_);
lean_dec_ref(v_termination_2110_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
v_a_2153_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2143_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2143_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2129_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_termination_2110_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
v_a_2161_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2141_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2141_);
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
lean_dec(v_a_2129_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_fixedParamPerms_2111_);
lean_dec_ref(v_termination_2110_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
lean_dec_ref(v_argsPacker_2100_);
lean_dec_ref(v_preDefs_2097_);
v_a_2169_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2132_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2132_);
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
lean_dec(v_a_2129_);
lean_dec(v_a_2123_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_fixedParamPerms_2111_);
lean_dec_ref(v_termination_2110_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
lean_dec_ref(v_argsPacker_2100_);
lean_dec_ref(v_preDefs_2097_);
v_a_2177_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2131_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2131_);
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
lean_dec(v_a_2123_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_fixedParamPerms_2111_);
lean_dec_ref(v_termination_2110_);
lean_dec_ref(v_value_2109_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
lean_dec_ref(v_argsPacker_2100_);
lean_dec_ref(v_preDefs_2097_);
v_a_2185_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2128_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2128_);
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
lean_dec(v_a_2123_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_fixedParamPerms_2111_);
lean_dec_ref(v_termination_2110_);
lean_dec_ref(v_value_2109_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
lean_dec_ref(v_argsPacker_2100_);
lean_dec_ref(v_preDefs_2097_);
v_a_2193_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2124_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2124_);
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
lean_dec(v_a_2121_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_fixedParamPerms_2111_);
lean_dec_ref(v_termination_2110_);
lean_dec_ref(v_value_2109_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
lean_dec_ref(v_argsPacker_2100_);
lean_dec_ref(v_preDefs_2097_);
v_a_2201_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2122_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2122_);
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
lean_dec_ref(v___x_2119_);
lean_dec_ref(v_ys_2112_);
lean_dec_ref(v_fixedParamPerms_2111_);
lean_dec_ref(v_termination_2110_);
lean_dec_ref(v_value_2109_);
lean_dec(v_numSectionVars_2108_);
lean_dec(v_binders_2107_);
lean_dec(v_newFn_2106_);
lean_dec_ref(v_modifiers_2105_);
lean_dec(v_levelParams_2104_);
lean_dec(v_ref_2102_);
lean_dec_ref(v_argsPacker_2100_);
lean_dec(v___x_2099_);
lean_dec_ref(v_preDefs_2097_);
v_a_2209_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2120_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2120_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2217_ = _args[0];
lean_object* v_perms_2218_ = _args[1];
lean_object* v___x_2219_ = _args[2];
lean_object* v_argsPacker_2220_ = _args[3];
lean_object* v___x_2221_ = _args[4];
lean_object* v_ref_2222_ = _args[5];
lean_object* v_kind_2223_ = _args[6];
lean_object* v_levelParams_2224_ = _args[7];
lean_object* v_modifiers_2225_ = _args[8];
lean_object* v_newFn_2226_ = _args[9];
lean_object* v_binders_2227_ = _args[10];
lean_object* v_numSectionVars_2228_ = _args[11];
lean_object* v_value_2229_ = _args[12];
lean_object* v_termination_2230_ = _args[13];
lean_object* v_fixedParamPerms_2231_ = _args[14];
lean_object* v_ys_2232_ = _args[15];
lean_object* v___y_2233_ = _args[16];
lean_object* v___y_2234_ = _args[17];
lean_object* v___y_2235_ = _args[18];
lean_object* v___y_2236_ = _args[19];
lean_object* v___y_2237_ = _args[20];
_start:
{
uint8_t v___x_2523__boxed_2238_; uint8_t v_kind_boxed_2239_; lean_object* v_res_2240_; 
v___x_2523__boxed_2238_ = lean_unbox(v___x_2221_);
v_kind_boxed_2239_ = lean_unbox(v_kind_2223_);
v_res_2240_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2217_, v_perms_2218_, v___x_2219_, v_argsPacker_2220_, v___x_2523__boxed_2238_, v_ref_2222_, v_kind_boxed_2239_, v_levelParams_2224_, v_modifiers_2225_, v_newFn_2226_, v_binders_2227_, v_numSectionVars_2228_, v_value_2229_, v_termination_2230_, v_fixedParamPerms_2231_, v_ys_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v_perms_2218_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2241_, lean_object* v_argsPacker_2242_, lean_object* v_preDefs_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_ref_2252_; uint8_t v_kind_2253_; lean_object* v_levelParams_2254_; lean_object* v_modifiers_2255_; lean_object* v_declName_2256_; lean_object* v_binders_2257_; lean_object* v_numSectionVars_2258_; lean_object* v_type_2259_; lean_object* v_value_2260_; lean_object* v_termination_2261_; lean_object* v_newFn_2262_; uint8_t v___x_2263_; 
v___x_2249_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = lean_array_get_borrowed(v___x_2249_, v_preDefs_2243_, v___x_2250_);
v_ref_2252_ = lean_ctor_get(v___x_2251_, 0);
v_kind_2253_ = lean_ctor_get_uint8(v___x_2251_, sizeof(void*)*9);
v_levelParams_2254_ = lean_ctor_get(v___x_2251_, 1);
v_modifiers_2255_ = lean_ctor_get(v___x_2251_, 2);
v_declName_2256_ = lean_ctor_get(v___x_2251_, 3);
v_binders_2257_ = lean_ctor_get(v___x_2251_, 4);
v_numSectionVars_2258_ = lean_ctor_get(v___x_2251_, 5);
v_type_2259_ = lean_ctor_get(v___x_2251_, 6);
v_value_2260_ = lean_ctor_get(v___x_2251_, 7);
v_termination_2261_ = lean_ctor_get(v___x_2251_, 8);
lean_inc_ref(v_fixedParamPerms_2241_);
v_newFn_2262_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2241_, v_argsPacker_2242_, v_preDefs_2243_);
v___x_2263_ = lean_name_eq(v_newFn_2262_, v_declName_2256_);
if (v___x_2263_ == 0)
{
lean_object* v_perms_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_inc_ref(v_termination_2261_);
lean_inc_ref(v_value_2260_);
lean_inc_ref(v_type_2259_);
lean_inc(v_numSectionVars_2258_);
lean_inc(v_binders_2257_);
lean_inc_ref(v_modifiers_2255_);
lean_inc(v_levelParams_2254_);
lean_inc(v_ref_2252_);
v_perms_2264_ = lean_ctor_get(v_fixedParamPerms_2241_, 1);
lean_inc_ref_n(v_perms_2264_, 2);
v___x_2265_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2266_ = lean_box(v___x_2263_);
v___x_2267_ = lean_box(v_kind_2253_);
v___f_2268_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 21, 15);
lean_closure_set(v___f_2268_, 0, v_preDefs_2243_);
lean_closure_set(v___f_2268_, 1, v_perms_2264_);
lean_closure_set(v___f_2268_, 2, v___x_2250_);
lean_closure_set(v___f_2268_, 3, v_argsPacker_2242_);
lean_closure_set(v___f_2268_, 4, v___x_2266_);
lean_closure_set(v___f_2268_, 5, v_ref_2252_);
lean_closure_set(v___f_2268_, 6, v___x_2267_);
lean_closure_set(v___f_2268_, 7, v_levelParams_2254_);
lean_closure_set(v___f_2268_, 8, v_modifiers_2255_);
lean_closure_set(v___f_2268_, 9, v_newFn_2262_);
lean_closure_set(v___f_2268_, 10, v_binders_2257_);
lean_closure_set(v___f_2268_, 11, v_numSectionVars_2258_);
lean_closure_set(v___f_2268_, 12, v_value_2260_);
lean_closure_set(v___f_2268_, 13, v_termination_2261_);
lean_closure_set(v___f_2268_, 14, v_fixedParamPerms_2241_);
v___x_2269_ = lean_array_get(v___x_2265_, v_perms_2264_, v___x_2250_);
lean_dec_ref(v_perms_2264_);
v___x_2270_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2269_, v_type_2259_, v___f_2268_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_inc(v___x_2251_);
lean_dec(v_newFn_2262_);
lean_dec_ref(v_preDefs_2243_);
lean_dec_ref(v_argsPacker_2242_);
lean_dec_ref(v_fixedParamPerms_2241_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2251_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2272_, lean_object* v_argsPacker_2273_, lean_object* v_preDefs_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2272_, v_argsPacker_2273_, v_preDefs_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2281_, lean_object* v_ys_2282_, lean_object* v_as_2283_, lean_object* v_i_2284_, lean_object* v_j_2285_, lean_object* v_inv_2286_, lean_object* v_bs_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2281_, v_ys_2282_, v_as_2283_, v_i_2284_, v_j_2285_, v_bs_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2294_, lean_object* v_ys_2295_, lean_object* v_as_2296_, lean_object* v_i_2297_, lean_object* v_j_2298_, lean_object* v_inv_2299_, lean_object* v_bs_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2294_, v_ys_2295_, v_as_2296_, v_i_2297_, v_j_2298_, v_inv_2299_, v_bs_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_as_2296_);
lean_dec_ref(v___x_2294_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2307_, lean_object* v_ys_2308_, lean_object* v_as_2309_, lean_object* v_i_2310_, lean_object* v_j_2311_, lean_object* v_inv_2312_, lean_object* v_bs_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2307_, v_ys_2308_, v_as_2309_, v_i_2310_, v_j_2311_, v_bs_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2320_, lean_object* v_ys_2321_, lean_object* v_as_2322_, lean_object* v_i_2323_, lean_object* v_j_2324_, lean_object* v_inv_2325_, lean_object* v_bs_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2320_, v_ys_2321_, v_as_2322_, v_i_2323_, v_j_2324_, v_inv_2325_, v_bs_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v_as_2322_);
lean_dec_ref(v___x_2320_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2333_, lean_object* v_k_2334_, uint8_t v_cleanupAnnotations_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___f_2341_; uint8_t v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2341_, 0, v_k_2334_);
v___x_2342_ = 1;
v___x_2343_ = 0;
v___x_2344_ = lean_box(0);
v___x_2345_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2333_, v___x_2342_, v___x_2343_, v___x_2342_, v___x_2343_, v___x_2344_, v___f_2341_, v_cleanupAnnotations_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2345_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2345_);
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
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2362_, lean_object* v_k_2363_, lean_object* v_cleanupAnnotations_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2370_; lean_object* v_res_2371_; 
v_cleanupAnnotations_boxed_2370_ = lean_unbox(v_cleanupAnnotations_2364_);
v_res_2371_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2362_, v_k_2363_, v_cleanupAnnotations_boxed_2370_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2372_, lean_object* v_e_2373_, lean_object* v_k_2374_, uint8_t v_cleanupAnnotations_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2373_, v_k_2374_, v_cleanupAnnotations_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_e_2383_, lean_object* v_k_2384_, lean_object* v_cleanupAnnotations_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2391_; lean_object* v_res_2392_; 
v_cleanupAnnotations_boxed_2391_ = lean_unbox(v_cleanupAnnotations_2385_);
v_res_2392_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2382_, v_e_2383_, v_k_2384_, v_cleanupAnnotations_boxed_2391_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___f_2399_; lean_object* v___x_1717__overap_2400_; lean_object* v___x_2401_; 
v___f_2399_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1717__overap_2400_ = lean_panic_fn_borrowed(v___f_2399_, v_msg_2393_);
lean_inc(v___y_2397_);
lean_inc_ref(v___y_2396_);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
v___x_2401_ = lean_apply_5(v___x_1717__overap_2400_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, lean_box(0));
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_array_get_size(v_xs_2409_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2418_, v_x_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec_ref(v_x_2419_);
lean_dec_ref(v_xs_2418_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2426_, size_t v_sz_2427_, size_t v_i_2428_, lean_object* v_b_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_a_2435_; uint8_t v___x_2439_; 
v___x_2439_ = lean_usize_dec_lt(v_i_2428_, v_sz_2427_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_b_2429_);
return v___x_2440_;
}
else
{
lean_object* v_snd_2441_; lean_object* v_fst_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2486_; 
v_snd_2441_ = lean_ctor_get(v_b_2429_, 1);
v_fst_2442_ = lean_ctor_get(v_b_2429_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_b_2429_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2444_ = v_b_2429_;
v_isShared_2445_ = v_isSharedCheck_2486_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_snd_2441_);
lean_inc(v_fst_2442_);
lean_dec(v_b_2429_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2486_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v_array_2446_; lean_object* v_start_2447_; lean_object* v_stop_2448_; uint8_t v___x_2449_; 
v_array_2446_ = lean_ctor_get(v_snd_2441_, 0);
v_start_2447_ = lean_ctor_get(v_snd_2441_, 1);
v_stop_2448_ = lean_ctor_get(v_snd_2441_, 2);
v___x_2449_ = lean_nat_dec_lt(v_start_2447_, v_stop_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2451_; 
if (v_isShared_2445_ == 0)
{
v___x_2451_ = v___x_2444_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_snd_2441_);
v___x_2451_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
}
else
{
lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2482_; 
lean_inc(v_stop_2448_);
lean_inc(v_start_2447_);
lean_inc_ref(v_array_2446_);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_snd_2441_);
if (v_isSharedCheck_2482_ == 0)
{
lean_object* v_unused_2483_; lean_object* v_unused_2484_; lean_object* v_unused_2485_; 
v_unused_2483_ = lean_ctor_get(v_snd_2441_, 2);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_snd_2441_, 1);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_snd_2441_, 0);
lean_dec(v_unused_2485_);
v___x_2455_ = v_snd_2441_;
v_isShared_2456_ = v_isSharedCheck_2482_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v_snd_2441_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2482_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2457_ = lean_array_fget(v_array_2446_, v_start_2447_);
v___x_2458_ = lean_unsigned_to_nat(1u);
v___x_2459_ = lean_nat_add(v_start_2447_, v___x_2458_);
lean_dec(v_start_2447_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___x_2459_);
v___x_2461_ = v___x_2455_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_array_2446_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_stop_2448_);
v___x_2461_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_a_2462_ = lean_array_uget_borrowed(v_as_2426_, v_i_2428_);
v___x_2463_ = l_Lean_Expr_fvarId_x21(v_a_2462_);
v___x_2464_ = l_Lean_FVarId_getUserName___redArg(v___x_2463_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = lean_array_push(v_fst_2442_, v_a_2465_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2461_);
lean_ctor_set(v___x_2444_, 0, v___x_2466_);
v___x_2468_ = v___x_2444_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2461_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
v_a_2435_ = v___x_2468_;
goto v___jp_2434_;
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v___x_2461_);
lean_del_object(v___x_2444_);
lean_dec(v_fst_2442_);
v_a_2470_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2464_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2464_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v___x_2479_; 
lean_dec_ref(v___x_2457_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 1, v___x_2461_);
v___x_2479_ = v___x_2444_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_fst_2442_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2461_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
v_a_2435_ = v___x_2479_;
goto v___jp_2434_;
}
}
}
}
}
}
}
v___jp_2434_:
{
size_t v___x_2436_; size_t v___x_2437_; 
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_add(v_i_2428_, v___x_2436_);
v_i_2428_ = v___x_2437_;
v_b_2429_ = v_a_2435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2487_, lean_object* v_sz_2488_, lean_object* v_i_2489_, lean_object* v_b_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
size_t v_sz_boxed_2495_; size_t v_i_boxed_2496_; lean_object* v_res_2497_; 
v_sz_boxed_2495_ = lean_unbox_usize(v_sz_2488_);
lean_dec(v_sz_2488_);
v_i_boxed_2496_ = lean_unbox_usize(v_i_2489_);
lean_dec(v_i_2489_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2487_, v_sz_boxed_2495_, v_i_boxed_2496_, v_b_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_as_2487_);
return v_res_2497_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2500_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2501_ = lean_unsigned_to_nat(4u);
v___x_2502_ = lean_unsigned_to_nat(119u);
v___x_2503_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2504_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2505_ = l_mkPanicMessageWithDecl(v___x_2504_, v___x_2503_, v___x_2502_, v___x_2501_, v___x_2500_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2507_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2508_ = lean_unsigned_to_nat(4u);
v___x_2509_ = lean_unsigned_to_nat(120u);
v___x_2510_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2511_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2512_ = l_mkPanicMessageWithDecl(v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_, v___x_2507_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2515_, lean_object* v_fixedParamPerms_2516_, lean_object* v_preDefIdx_2517_, lean_object* v_xs_2518_, lean_object* v_x_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = lean_array_get_size(v_xs_2518_);
v___x_2526_ = lean_nat_dec_eq(v___x_2525_, v_a_2515_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2528_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2527_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v___x_2528_;
}
else
{
lean_object* v_perms_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_perms_2529_ = lean_ctor_get(v_fixedParamPerms_2516_, 1);
v___x_2530_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2531_ = lean_array_get_borrowed(v___x_2530_, v_perms_2529_, v_preDefIdx_2517_);
v___x_2532_ = lean_array_get_size(v___x_2531_);
v___x_2533_ = lean_nat_dec_eq(v___x_2532_, v_a_2515_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2535_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2534_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; size_t v_sz_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2531_);
v___x_2538_ = l_Array_toSubarray___redArg(v___x_2531_, v___x_2536_, v___x_2532_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v_sz_2540_ = lean_array_size(v_xs_2518_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2518_, v_sz_2540_, v___x_2541_, v___x_2539_, v___y_2520_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2551_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2551_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_fst_2547_; lean_object* v___x_2549_; 
v_fst_2547_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fst_2547_);
lean_dec(v_a_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v_fst_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_fst_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2552_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2542_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2542_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2560_, lean_object* v_fixedParamPerms_2561_, lean_object* v_preDefIdx_2562_, lean_object* v_xs_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2560_, v_fixedParamPerms_2561_, v_preDefIdx_2562_, v_xs_2563_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v_x_2564_);
lean_dec_ref(v_xs_2563_);
lean_dec(v_preDefIdx_2562_);
lean_dec_ref(v_fixedParamPerms_2561_);
lean_dec(v_a_2560_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2572_, lean_object* v_preDefIdx_2573_, lean_object* v_preDef_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_type_2580_; lean_object* v_value_2581_; lean_object* v___f_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; 
v_type_2580_ = lean_ctor_get(v_preDef_2574_, 6);
lean_inc_ref(v_type_2580_);
v_value_2581_ = lean_ctor_get(v_preDef_2574_, 7);
lean_inc_ref(v_value_2581_);
lean_dec_ref(v_preDef_2574_);
v___f_2582_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2583_ = 0;
v___x_2584_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2581_, v___f_2582_, v___x_2583_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_n(v_a_2585_, 2);
lean_dec_ref(v___x_2584_);
v___f_2586_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2586_, 0, v_a_2585_);
lean_closure_set(v___f_2586_, 1, v_fixedParamPerms_2572_);
lean_closure_set(v___f_2586_, 2, v_preDefIdx_2573_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2585_);
v___x_2588_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2580_, v___x_2587_, v___f_2586_, v___x_2583_, v___x_2583_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
return v___x_2588_;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_type_2580_);
lean_dec(v_preDefIdx_2573_);
lean_dec_ref(v_fixedParamPerms_2572_);
v_a_2589_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2584_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2584_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2597_, lean_object* v_preDefIdx_2598_, lean_object* v_preDef_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2597_, v_preDefIdx_2598_, v_preDef_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2606_, size_t v_sz_2607_, size_t v_i_2608_, lean_object* v_b_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2606_, v_sz_2607_, v_i_2608_, v_b_2609_, v___y_2610_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2616_, lean_object* v_sz_2617_, lean_object* v_i_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
size_t v_sz_boxed_2625_; size_t v_i_boxed_2626_; lean_object* v_res_2627_; 
v_sz_boxed_2625_ = lean_unbox_usize(v_sz_2617_);
lean_dec(v_sz_2617_);
v_i_boxed_2626_ = lean_unbox_usize(v_i_2618_);
lean_dec(v_i_2618_);
v_res_2627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2616_, v_sz_boxed_2625_, v_i_boxed_2626_, v_b_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec_ref(v_as_2616_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___f_2634_; lean_object* v___x_1723__overap_2635_; lean_object* v___x_2636_; 
v___f_2634_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1723__overap_2635_ = lean_panic_fn_borrowed(v___f_2634_, v_msg_2628_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
v___x_2636_ = lean_apply_5(v___x_1723__overap_2635_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, lean_box(0));
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2643_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2644_; double v___x_2645_; 
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_float_of_nat(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2649_, lean_object* v_msg_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_ref_2656_; lean_object* v___x_2657_; lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2702_; 
v_ref_2656_ = lean_ctor_get(v___y_2653_, 5);
v___x_2657_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2702_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2702_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v_traceState_2663_; lean_object* v_env_2664_; lean_object* v_nextMacroScope_2665_; lean_object* v_ngen_2666_; lean_object* v_auxDeclNGen_2667_; lean_object* v_cache_2668_; lean_object* v_messages_2669_; lean_object* v_infoState_2670_; lean_object* v_snapshotTasks_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2701_; 
v___x_2662_ = lean_st_ref_take(v___y_2654_);
v_traceState_2663_ = lean_ctor_get(v___x_2662_, 4);
v_env_2664_ = lean_ctor_get(v___x_2662_, 0);
v_nextMacroScope_2665_ = lean_ctor_get(v___x_2662_, 1);
v_ngen_2666_ = lean_ctor_get(v___x_2662_, 2);
v_auxDeclNGen_2667_ = lean_ctor_get(v___x_2662_, 3);
v_cache_2668_ = lean_ctor_get(v___x_2662_, 5);
v_messages_2669_ = lean_ctor_get(v___x_2662_, 6);
v_infoState_2670_ = lean_ctor_get(v___x_2662_, 7);
v_snapshotTasks_2671_ = lean_ctor_get(v___x_2662_, 8);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2673_ = v___x_2662_;
v_isShared_2674_ = v_isSharedCheck_2701_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_snapshotTasks_2671_);
lean_inc(v_infoState_2670_);
lean_inc(v_messages_2669_);
lean_inc(v_cache_2668_);
lean_inc(v_traceState_2663_);
lean_inc(v_auxDeclNGen_2667_);
lean_inc(v_ngen_2666_);
lean_inc(v_nextMacroScope_2665_);
lean_inc(v_env_2664_);
lean_dec(v___x_2662_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2701_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
uint64_t v_tid_2675_; lean_object* v_traces_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2700_; 
v_tid_2675_ = lean_ctor_get_uint64(v_traceState_2663_, sizeof(void*)*1);
v_traces_2676_ = lean_ctor_get(v_traceState_2663_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_traceState_2663_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2678_ = v_traceState_2663_;
v_isShared_2679_ = v_isSharedCheck_2700_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_traces_2676_);
lean_dec(v_traceState_2663_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2700_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; double v___x_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2682_ = 0;
v___x_2683_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2684_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2684_, 0, v_cls_2649_);
lean_ctor_set(v___x_2684_, 1, v___x_2680_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
lean_ctor_set_float(v___x_2684_, sizeof(void*)*3, v___x_2681_);
lean_ctor_set_float(v___x_2684_, sizeof(void*)*3 + 8, v___x_2681_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*3 + 16, v___x_2682_);
v___x_2685_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2686_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v_a_2658_);
lean_ctor_set(v___x_2686_, 2, v___x_2685_);
lean_inc(v_ref_2656_);
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v_ref_2656_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_PersistentArray_push___redArg(v_traces_2676_, v___x_2687_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2688_);
v___x_2690_ = v___x_2678_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2688_);
lean_ctor_set_uint64(v_reuseFailAlloc_2699_, sizeof(void*)*1, v_tid_2675_);
v___x_2690_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2692_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 4, v___x_2690_);
v___x_2692_ = v___x_2673_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_env_2664_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_nextMacroScope_2665_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_ngen_2666_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_auxDeclNGen_2667_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_cache_2668_);
lean_ctor_set(v_reuseFailAlloc_2698_, 6, v_messages_2669_);
lean_ctor_set(v_reuseFailAlloc_2698_, 7, v_infoState_2670_);
lean_ctor_set(v_reuseFailAlloc_2698_, 8, v_snapshotTasks_2671_);
v___x_2692_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2693_ = lean_st_ref_set(v___y_2654_, v___x_2692_);
v___x_2694_ = lean_box(0);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2694_);
v___x_2696_ = v___x_2660_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2703_, lean_object* v_msg_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2703_, v_msg_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2710_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2713_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2714_ = lean_unsigned_to_nat(8u);
v___x_2715_ = lean_unsigned_to_nat(135u);
v___x_2716_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2717_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2718_ = l_mkPanicMessageWithDecl(v___x_2717_, v___x_2716_, v___x_2715_, v___x_2714_, v___x_2713_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2719_, lean_object* v_unaryPreDefNonRec_2720_, lean_object* v___x_2721_, lean_object* v_us_2722_, lean_object* v_argsPacker_2723_, lean_object* v_j_2724_, uint8_t v_isZero_2725_, lean_object* v_params_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_array_get_size(v_params_2726_);
v___x_2734_ = lean_nat_dec_eq(v___x_2719_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v_j_2724_);
lean_dec(v_us_2722_);
lean_dec_ref(v_unaryPreDefNonRec_2720_);
v___x_2735_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2736_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2735_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v___x_2736_;
}
else
{
lean_object* v_declName_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v_declName_2737_ = lean_ctor_get(v_unaryPreDefNonRec_2720_, 3);
lean_inc(v_declName_2737_);
lean_dec_ref(v_unaryPreDefNonRec_2720_);
v___x_2738_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2721_, v_params_2726_);
v___x_2739_ = l_Lean_mkConst(v_declName_2737_, v_us_2722_);
v___x_2740_ = l_Lean_mkAppN(v___x_2739_, v___x_2738_);
lean_dec_ref(v___x_2738_);
v___x_2741_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2723_, v___x_2740_, v_j_2724_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2721_, v_params_2726_);
v___x_2744_ = l_Lean_Expr_beta(v_a_2742_, v___x_2743_);
v___x_2745_ = 1;
v___x_2746_ = l_Lean_Meta_mkLambdaFVars(v_params_2726_, v___x_2744_, v_isZero_2725_, v___x_2734_, v_isZero_2725_, v___x_2734_, v___x_2745_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v___x_2746_;
}
else
{
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2747_, lean_object* v_unaryPreDefNonRec_2748_, lean_object* v___x_2749_, lean_object* v_us_2750_, lean_object* v_argsPacker_2751_, lean_object* v_j_2752_, lean_object* v_isZero_2753_, lean_object* v_params_2754_, lean_object* v_x_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v_isZero_boxed_2761_; lean_object* v_res_2762_; 
v_isZero_boxed_2761_ = lean_unbox(v_isZero_2753_);
v_res_2762_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2747_, v_unaryPreDefNonRec_2748_, v___x_2749_, v_us_2750_, v_argsPacker_2751_, v_j_2752_, v_isZero_boxed_2761_, v_params_2754_, v_x_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec_ref(v_x_2755_);
lean_dec_ref(v_params_2754_);
lean_dec_ref(v_argsPacker_2751_);
lean_dec_ref(v___x_2749_);
lean_dec(v___x_2747_);
return v_res_2762_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2774_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2775_ = l_Lean_Name_append(v___x_2774_, v___x_2773_);
return v___x_2775_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2779_, lean_object* v_unaryPreDefNonRec_2780_, lean_object* v_us_2781_, lean_object* v_argsPacker_2782_, lean_object* v_as_2783_, lean_object* v_i_2784_, lean_object* v_j_2785_, lean_object* v_bs_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_zero_2792_; uint8_t v_isZero_2793_; 
v_zero_2792_ = lean_unsigned_to_nat(0u);
v_isZero_2793_ = lean_nat_dec_eq(v_i_2784_, v_zero_2792_);
if (v_isZero_2793_ == 1)
{
lean_object* v___x_2794_; 
lean_dec(v_j_2785_);
lean_dec(v_i_2784_);
lean_dec_ref(v_argsPacker_2782_);
lean_dec(v_us_2781_);
lean_dec_ref(v_unaryPreDefNonRec_2780_);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_bs_2786_);
return v___x_2794_;
}
else
{
lean_object* v_perms_2795_; lean_object* v___x_2796_; lean_object* v_ref_2797_; uint8_t v_kind_2798_; lean_object* v_levelParams_2799_; lean_object* v_modifiers_2800_; lean_object* v_declName_2801_; lean_object* v_binders_2802_; lean_object* v_numSectionVars_2803_; lean_object* v_type_2804_; lean_object* v_termination_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2854_; 
v_perms_2795_ = lean_ctor_get(v_fixedParamPerms_2779_, 1);
v___x_2796_ = lean_array_fget(v_as_2783_, v_j_2785_);
v_ref_2797_ = lean_ctor_get(v___x_2796_, 0);
v_kind_2798_ = lean_ctor_get_uint8(v___x_2796_, sizeof(void*)*9);
v_levelParams_2799_ = lean_ctor_get(v___x_2796_, 1);
v_modifiers_2800_ = lean_ctor_get(v___x_2796_, 2);
v_declName_2801_ = lean_ctor_get(v___x_2796_, 3);
v_binders_2802_ = lean_ctor_get(v___x_2796_, 4);
v_numSectionVars_2803_ = lean_ctor_get(v___x_2796_, 5);
v_type_2804_ = lean_ctor_get(v___x_2796_, 6);
v_termination_2805_ = lean_ctor_get(v___x_2796_, 8);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; 
v_unused_2855_ = lean_ctor_get(v___x_2796_, 7);
lean_dec(v_unused_2855_);
v___x_2807_ = v___x_2796_;
v_isShared_2808_ = v_isSharedCheck_2854_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_termination_2805_);
lean_inc(v_type_2804_);
lean_inc(v_numSectionVars_2803_);
lean_inc(v_binders_2802_);
lean_inc(v_declName_2801_);
lean_inc(v_modifiers_2800_);
lean_inc(v_levelParams_2799_);
lean_inc(v_ref_2797_);
lean_dec(v___x_2796_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2854_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2809_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2810_ = lean_array_get_borrowed(v___x_2809_, v_perms_2795_, v_j_2785_);
v___x_2811_ = lean_array_get_size(v___x_2810_);
v___x_2812_ = lean_box(v_isZero_2793_);
lean_inc(v_j_2785_);
lean_inc_ref(v_argsPacker_2782_);
lean_inc(v_us_2781_);
lean_inc(v___x_2810_);
lean_inc_ref(v_unaryPreDefNonRec_2780_);
v___f_2813_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2813_, 0, v___x_2811_);
lean_closure_set(v___f_2813_, 1, v_unaryPreDefNonRec_2780_);
lean_closure_set(v___f_2813_, 2, v___x_2810_);
lean_closure_set(v___f_2813_, 3, v_us_2781_);
lean_closure_set(v___f_2813_, 4, v_argsPacker_2782_);
lean_closure_set(v___f_2813_, 5, v_j_2785_);
lean_closure_set(v___f_2813_, 6, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2811_);
lean_inc_ref(v_type_2804_);
v___x_2815_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2804_, v___x_2814_, v___f_2813_, v_isZero_2793_, v_isZero_2793_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_options_2816_; lean_object* v_a_2817_; lean_object* v_inheritedTraceOptions_2818_; uint8_t v_hasTrace_2819_; lean_object* v_one_2820_; lean_object* v_n_2821_; 
v_options_2816_ = lean_ctor_get(v___y_2789_, 2);
v_a_2817_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2815_);
v_inheritedTraceOptions_2818_ = lean_ctor_get(v___y_2789_, 13);
v_hasTrace_2819_ = lean_ctor_get_uint8(v_options_2816_, sizeof(void*)*1);
v_one_2820_ = lean_unsigned_to_nat(1u);
v_n_2821_ = lean_nat_sub(v_i_2784_, v_one_2820_);
lean_dec(v_i_2784_);
if (v_hasTrace_2819_ == 0)
{
goto v___jp_2822_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2830_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2818_, v_options_2816_, v___x_2830_);
if (v___x_2831_ == 0)
{
goto v___jp_2822_;
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_inc(v_declName_2801_);
v___x_2832_ = l_Lean_MessageData_ofName(v_declName_2801_);
v___x_2833_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
lean_inc(v_a_2817_);
v___x_2835_ = l_Lean_MessageData_ofExpr(v_a_2817_);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2829_, v___x_2836_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_dec_ref(v___x_2837_);
goto v___jp_2822_;
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_n_2821_);
lean_dec(v_a_2817_);
lean_del_object(v___x_2807_);
lean_dec_ref(v_termination_2805_);
lean_dec_ref(v_type_2804_);
lean_dec(v_numSectionVars_2803_);
lean_dec(v_binders_2802_);
lean_dec(v_declName_2801_);
lean_dec_ref(v_modifiers_2800_);
lean_dec(v_levelParams_2799_);
lean_dec(v_ref_2797_);
lean_dec_ref(v_bs_2786_);
lean_dec(v_j_2785_);
lean_dec_ref(v_argsPacker_2782_);
lean_dec(v_us_2781_);
lean_dec_ref(v_unaryPreDefNonRec_2780_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
v___jp_2822_:
{
lean_object* v___x_2824_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 7, v_a_2817_);
v___x_2824_ = v___x_2807_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_ref_2797_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_levelParams_2799_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_modifiers_2800_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_declName_2801_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_binders_2802_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_numSectionVars_2803_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v_type_2804_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_a_2817_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v_termination_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*9, v_kind_2798_);
v___x_2824_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_nat_add(v_j_2785_, v_one_2820_);
lean_dec(v_j_2785_);
v___x_2826_ = lean_array_push(v_bs_2786_, v___x_2824_);
v_i_2784_ = v_n_2821_;
v_j_2785_ = v___x_2825_;
v_bs_2786_ = v___x_2826_;
goto _start;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_del_object(v___x_2807_);
lean_dec_ref(v_termination_2805_);
lean_dec_ref(v_type_2804_);
lean_dec(v_numSectionVars_2803_);
lean_dec(v_binders_2802_);
lean_dec(v_declName_2801_);
lean_dec_ref(v_modifiers_2800_);
lean_dec(v_levelParams_2799_);
lean_dec(v_ref_2797_);
lean_dec_ref(v_bs_2786_);
lean_dec(v_j_2785_);
lean_dec(v_i_2784_);
lean_dec_ref(v_argsPacker_2782_);
lean_dec(v_us_2781_);
lean_dec_ref(v_unaryPreDefNonRec_2780_);
v_a_2846_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2815_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2815_);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2856_, lean_object* v_unaryPreDefNonRec_2857_, lean_object* v_us_2858_, lean_object* v_argsPacker_2859_, lean_object* v_as_2860_, lean_object* v_i_2861_, lean_object* v_j_2862_, lean_object* v_bs_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2856_, v_unaryPreDefNonRec_2857_, v_us_2858_, v_argsPacker_2859_, v_as_2860_, v_i_2861_, v_j_2862_, v_bs_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_as_2860_);
lean_dec_ref(v_fixedParamPerms_2856_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2870_, lean_object* v_preDefs_2871_, lean_object* v_fixedParamPerms_2872_, lean_object* v_us_2873_, lean_object* v_argsPacker_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2870_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref(v___x_2880_);
v___x_2881_ = lean_array_get_size(v_preDefs_2871_);
v___x_2882_ = lean_unsigned_to_nat(0u);
v___x_2883_ = lean_mk_empty_array_with_capacity(v___x_2881_);
v___x_2884_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2872_, v_unaryPreDefNonRec_2870_, v_us_2873_, v_argsPacker_2874_, v_preDefs_2871_, v___x_2881_, v___x_2882_, v___x_2883_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2884_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec_ref(v_argsPacker_2874_);
lean_dec(v_us_2873_);
lean_dec_ref(v_unaryPreDefNonRec_2870_);
v_a_2885_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2880_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2880_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2893_, lean_object* v_preDefs_2894_, lean_object* v_fixedParamPerms_2895_, lean_object* v_us_2896_, lean_object* v_argsPacker_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2893_, v_preDefs_2894_, v_fixedParamPerms_2895_, v_us_2896_, v_argsPacker_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_fixedParamPerms_2895_);
lean_dec_ref(v_preDefs_2894_);
return v_res_2903_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2904_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
return v___x_2906_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
return v___x_2908_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2910_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
lean_ctor_set(v___x_2910_, 2, v___x_2909_);
lean_ctor_set(v___x_2910_, 3, v___x_2909_);
lean_ctor_set(v___x_2910_, 4, v___x_2909_);
lean_ctor_set(v___x_2910_, 5, v___x_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; lean_object* v_nextMacroScope_2916_; lean_object* v_ngen_2917_; lean_object* v_auxDeclNGen_2918_; lean_object* v_traceState_2919_; lean_object* v_messages_2920_; lean_object* v_infoState_2921_; lean_object* v_snapshotTasks_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2948_; 
v___x_2915_ = lean_st_ref_take(v___y_2913_);
v_nextMacroScope_2916_ = lean_ctor_get(v___x_2915_, 1);
v_ngen_2917_ = lean_ctor_get(v___x_2915_, 2);
v_auxDeclNGen_2918_ = lean_ctor_get(v___x_2915_, 3);
v_traceState_2919_ = lean_ctor_get(v___x_2915_, 4);
v_messages_2920_ = lean_ctor_get(v___x_2915_, 6);
v_infoState_2921_ = lean_ctor_get(v___x_2915_, 7);
v_snapshotTasks_2922_ = lean_ctor_get(v___x_2915_, 8);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; 
v_unused_2949_ = lean_ctor_get(v___x_2915_, 5);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v___x_2915_, 0);
lean_dec(v_unused_2950_);
v___x_2924_ = v___x_2915_;
v_isShared_2925_ = v_isSharedCheck_2948_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_snapshotTasks_2922_);
lean_inc(v_infoState_2921_);
lean_inc(v_messages_2920_);
lean_inc(v_traceState_2919_);
lean_inc(v_auxDeclNGen_2918_);
lean_inc(v_ngen_2917_);
lean_inc(v_nextMacroScope_2916_);
lean_dec(v___x_2915_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2948_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 5, v___x_2926_);
lean_ctor_set(v___x_2924_, 0, v_env_2911_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_env_2911_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_nextMacroScope_2916_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_ngen_2917_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_auxDeclNGen_2918_);
lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_traceState_2919_);
lean_ctor_set(v_reuseFailAlloc_2947_, 5, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2947_, 6, v_messages_2920_);
lean_ctor_set(v_reuseFailAlloc_2947_, 7, v_infoState_2921_);
lean_ctor_set(v_reuseFailAlloc_2947_, 8, v_snapshotTasks_2922_);
v___x_2928_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_mctx_2931_; lean_object* v_zetaDeltaFVarIds_2932_; lean_object* v_postponed_2933_; lean_object* v_diag_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2945_; 
v___x_2929_ = lean_st_ref_set(v___y_2913_, v___x_2928_);
v___x_2930_ = lean_st_ref_take(v___y_2912_);
v_mctx_2931_ = lean_ctor_get(v___x_2930_, 0);
v_zetaDeltaFVarIds_2932_ = lean_ctor_get(v___x_2930_, 2);
v_postponed_2933_ = lean_ctor_get(v___x_2930_, 3);
v_diag_2934_ = lean_ctor_get(v___x_2930_, 4);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v___x_2930_, 1);
lean_dec(v_unused_2946_);
v___x_2936_ = v___x_2930_;
v_isShared_2937_ = v_isSharedCheck_2945_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_diag_2934_);
lean_inc(v_postponed_2933_);
lean_inc(v_zetaDeltaFVarIds_2932_);
lean_inc(v_mctx_2931_);
lean_dec(v___x_2930_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2945_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_mctx_2931_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_zetaDeltaFVarIds_2932_);
lean_ctor_set(v_reuseFailAlloc_2944_, 3, v_postponed_2933_);
lean_ctor_set(v_reuseFailAlloc_2944_, 4, v_diag_2934_);
v___x_2940_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_st_ref_set(v___y_2912_, v___x_2940_);
v___x_2942_ = lean_box(0);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2956_, lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v_env_2964_; lean_object* v_a_2966_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2963_ = lean_st_ref_get(v___y_2961_);
v_env_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_ref(v_env_2964_);
lean_dec(v___x_2963_);
v___x_2976_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2956_, v___y_2959_, v___y_2961_);
lean_dec_ref(v___x_2976_);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
v___x_2977_ = lean_apply_5(v_x_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2964_, v___y_2959_, v___y_2961_);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_2987_);
v___x_2981_ = v___x_2979_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v___x_2979_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v_a_2978_);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2978_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
else
{
lean_object* v_a_2988_; 
v_a_2988_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2988_);
lean_dec_ref(v___x_2977_);
v_a_2966_ = v_a_2988_;
goto v___jp_2965_;
}
v___jp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v___x_2967_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2964_, v___y_2959_, v___y_2961_);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v___x_2967_, 0);
lean_dec(v_unused_2975_);
v___x_2969_ = v___x_2967_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v___x_2967_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 1);
lean_ctor_set(v___x_2969_, 0, v_a_2966_);
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2966_);
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
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_2989_, lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_2989_, v_x_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_2997_, lean_object* v_argsPacker_2998_, lean_object* v_preDefs_2999_, lean_object* v_unaryPreDefNonRec_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v_levelParams_3007_; lean_object* v_env_3008_; lean_object* v___x_3009_; lean_object* v_us_3010_; lean_object* v___f_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3006_ = lean_st_ref_get(v_a_3004_);
v_levelParams_3007_ = lean_ctor_get(v_unaryPreDefNonRec_3000_, 1);
v_env_3008_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_env_3008_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
lean_inc(v_levelParams_3007_);
v_us_3010_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3007_, v___x_3009_);
v___f_3011_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3011_, 0, v_unaryPreDefNonRec_3000_);
lean_closure_set(v___f_3011_, 1, v_preDefs_2999_);
lean_closure_set(v___f_3011_, 2, v_fixedParamPerms_2997_);
lean_closure_set(v___f_3011_, 3, v_us_3010_);
lean_closure_set(v___f_3011_, 4, v_argsPacker_2998_);
v___x_3012_ = l_Lean_Environment_unlockAsync(v_env_3008_);
v___x_3013_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3012_, v___f_3011_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3014_, lean_object* v_argsPacker_3015_, lean_object* v_preDefs_3016_, lean_object* v_unaryPreDefNonRec_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3014_, v_argsPacker_3015_, v_preDefs_3016_, v_unaryPreDefNonRec_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3024_, lean_object* v_unaryPreDefNonRec_3025_, lean_object* v_us_3026_, lean_object* v_argsPacker_3027_, lean_object* v_as_3028_, lean_object* v_i_3029_, lean_object* v_j_3030_, lean_object* v_inv_3031_, lean_object* v_bs_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3024_, v_unaryPreDefNonRec_3025_, v_us_3026_, v_argsPacker_3027_, v_as_3028_, v_i_3029_, v_j_3030_, v_bs_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3039_, lean_object* v_unaryPreDefNonRec_3040_, lean_object* v_us_3041_, lean_object* v_argsPacker_3042_, lean_object* v_as_3043_, lean_object* v_i_3044_, lean_object* v_j_3045_, lean_object* v_inv_3046_, lean_object* v_bs_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3039_, v_unaryPreDefNonRec_3040_, v_us_3041_, v_argsPacker_3042_, v_as_3043_, v_i_3044_, v_j_3045_, v_inv_3046_, v_bs_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v_as_3043_);
lean_dec_ref(v_fixedParamPerms_3039_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3054_, v___y_3056_, v___y_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3068_, lean_object* v_env_3069_, lean_object* v_x_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3069_, v_x_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3077_, lean_object* v_env_3078_, lean_object* v_x_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3077_, v_env_3078_, v_x_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
return v_res_3085_;
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
