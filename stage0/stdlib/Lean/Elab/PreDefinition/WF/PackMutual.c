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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___f_260_; lean_object* v___x_1331__overap_261_; lean_object* v___x_262_; 
v___f_260_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1331__overap_261_ = lean_panic_fn_borrowed(v___f_260_, v_msg_254_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_262_ = lean_apply_5(v___x_1331__overap_261_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
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
v___y_368_ = v___x_359_;
goto v___jp_367_;
}
else
{
lean_dec_ref_known(v_v_364_, 1);
v___y_368_ = v___x_363_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2___boxed(lean_object* v___x_374_, lean_object* v_sz_375_, lean_object* v_i_376_, lean_object* v_bs_377_){
_start:
{
uint8_t v___x_9806__boxed_378_; size_t v_sz_boxed_379_; size_t v_i_boxed_380_; lean_object* v_res_381_; 
v___x_9806__boxed_378_ = lean_unbox(v___x_374_);
v_sz_boxed_379_ = lean_unbox_usize(v_sz_375_);
lean_dec(v_sz_375_);
v_i_boxed_380_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_9806__boxed_378_, v_sz_boxed_379_, v_i_boxed_380_, v_bs_377_);
return v_res_381_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_385_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__2));
v___x_386_ = lean_unsigned_to_nat(6u);
v___x_387_ = lean_unsigned_to_nat(55u);
v___x_388_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__1));
v___x_389_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_390_ = l_mkPanicMessageWithDecl(v___x_389_, v___x_388_, v___x_387_, v___x_386_, v___x_385_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Array_instInhabited(lean_box(0));
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___lam__2(lean_object* v_funNames_392_, lean_object* v_fixedParamPerms_393_, lean_object* v_argsPacker_394_, lean_object* v___x_395_, lean_object* v_newF_396_, lean_object* v_e_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_403_ = l_Lean_Expr_getAppFn(v_e_397_);
v___x_404_ = l_Lean_Expr_isConst(v___x_403_);
v___x_405_ = lean_bool_not(v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = l_Lean_Expr_constName_x21(v___x_403_);
lean_dec_ref(v___x_403_);
v___x_407_ = l_Array_idxOf_x3f___at___00Lean_Elab_WF_packCalls_spec__0(v_funNames_392_, v___x_406_);
lean_dec(v___x_406_);
if (lean_obj_tag(v___x_407_) == 1)
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_444_; 
v_val_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_444_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_444_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_444_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_perms_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_perms_412_ = lean_ctor_get(v_fixedParamPerms_393_, 1);
v___x_413_ = lean_array_get_size(v_perms_412_);
v___x_414_ = lean_nat_dec_lt(v_val_408_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_del_object(v___x_410_);
lean_dec(v_val_408_);
lean_dec_ref(v_e_397_);
lean_dec_ref(v_newF_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_argsPacker_394_);
v___x_415_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__3, &l_Lean_Elab_WF_packCalls___lam__2___closed__3_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__3);
v___x_416_ = l_panic___at___00Lean_Elab_WF_packCalls_spec__1(v___x_415_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___f_419_; size_t v_sz_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_417_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_418_ = lean_array_get_borrowed(v___x_417_, v_perms_412_, v_val_408_);
lean_inc_n(v___x_418_, 2);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__1___boxed), 11, 5);
lean_closure_set(v___f_419_, 0, v___x_418_);
lean_closure_set(v___f_419_, 1, v_argsPacker_394_);
lean_closure_set(v___f_419_, 2, v___x_395_);
lean_closure_set(v___f_419_, 3, v_val_408_);
lean_closure_set(v___f_419_, 4, v_newF_396_);
v_sz_420_ = lean_array_size(v___x_418_);
v___x_421_ = ((size_t)0ULL);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packCalls_spec__2(v___x_405_, v_sz_420_, v___x_421_, v___x_418_);
v___x_423_ = lean_array_get_size(v___x_422_);
lean_dec_ref(v___x_422_);
v___x_424_ = l_Lean_Elab_WF_withAppN(v___x_423_, v_e_397_, v___f_419_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_435_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_435_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 0);
lean_ctor_set(v___x_410_, 0, v_a_425_);
v___x_430_ = v___x_410_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_430_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_del_object(v___x_410_);
v_a_436_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_424_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_424_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v___x_407_);
lean_dec_ref(v_newF_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_argsPacker_394_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_e_397_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v___x_403_);
lean_dec_ref(v_newF_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_argsPacker_394_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_e_397_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
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
lean_object* v___y_506_; lean_object* v_fileName_515_; lean_object* v_fileMap_516_; lean_object* v_options_517_; lean_object* v_currRecDepth_518_; lean_object* v_maxRecDepth_519_; lean_object* v_ref_520_; lean_object* v_currNamespace_521_; lean_object* v_openDecls_522_; lean_object* v_initHeartbeats_523_; lean_object* v_maxHeartbeats_524_; lean_object* v_quotContext_525_; lean_object* v_currMacroScope_526_; uint8_t v_diag_527_; lean_object* v_cancelTk_x3f_528_; uint8_t v_suppressElabErrors_529_; lean_object* v_inheritedTraceOptions_530_; uint8_t v___y_532_; lean_object* v___x_538_; uint8_t v___x_539_; uint8_t v___x_540_; 
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
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v_maxRecDepth_519_, v___x_538_);
v___x_540_ = lean_bool_not(v___x_539_);
if (v___x_540_ == 0)
{
v___y_532_ = v___x_540_;
goto v___jp_531_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = lean_nat_dec_eq(v_currRecDepth_518_, v_maxRecDepth_519_);
v___y_532_ = v___x_541_;
goto v___jp_531_;
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
v___jp_531_:
{
if (v___y_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_currRecDepth_518_, v___x_533_);
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
v___x_535_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_535_, 0, v_fileName_515_);
lean_ctor_set(v___x_535_, 1, v_fileMap_516_);
lean_ctor_set(v___x_535_, 2, v_options_517_);
lean_ctor_set(v___x_535_, 3, v___x_534_);
lean_ctor_set(v___x_535_, 4, v_maxRecDepth_519_);
lean_ctor_set(v___x_535_, 5, v_ref_520_);
lean_ctor_set(v___x_535_, 6, v_currNamespace_521_);
lean_ctor_set(v___x_535_, 7, v_openDecls_522_);
lean_ctor_set(v___x_535_, 8, v_initHeartbeats_523_);
lean_ctor_set(v___x_535_, 9, v_maxHeartbeats_524_);
lean_ctor_set(v___x_535_, 10, v_quotContext_525_);
lean_ctor_set(v___x_535_, 11, v_currMacroScope_526_);
lean_ctor_set(v___x_535_, 12, v_cancelTk_x3f_528_);
lean_ctor_set(v___x_535_, 13, v_inheritedTraceOptions_530_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*14, v_diag_527_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*14 + 1, v_suppressElabErrors_529_);
lean_inc(v___y_503_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
v___x_536_ = lean_apply_6(v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___x_535_, v___y_503_, lean_box(0));
v___y_506_ = v___x_536_;
goto v___jp_505_;
}
else
{
lean_object* v___x_537_; 
lean_dec_ref(v_x_498_);
lean_inc(v_ref_520_);
v___x_537_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_520_);
v___y_506_ = v___x_537_;
goto v___jp_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg___boxed(lean_object* v_x_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(lean_object* v___x_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_550_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2___boxed(lean_object* v___x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___lam__2(v___x_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(lean_object* v_k_564_, lean_object* v___y_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_565_);
v___x_572_ = lean_apply_7(v_k_564_, v_b_566_, v___y_565_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, lean_box(0));
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed(lean_object* v_k_573_, lean_object* v___y_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0(v_k_573_, v___y_574_, v_b_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(lean_object* v_name_582_, lean_object* v_type_583_, lean_object* v_val_584_, lean_object* v_k_585_, uint8_t v_nondep_586_, uint8_t v_kind_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___f_594_; lean_object* v___x_595_; 
lean_inc(v___y_588_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_594_, 0, v_k_585_);
lean_closure_set(v___f_594_, 1, v___y_588_);
v___x_595_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_582_, v_type_583_, v_val_584_, v___f_594_, v_nondep_586_, v_kind_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_595_) == 0)
{
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg___boxed(lean_object* v_name_604_, lean_object* v_type_605_, lean_object* v_val_606_, lean_object* v_k_607_, lean_object* v_nondep_608_, lean_object* v_kind_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
uint8_t v_nondep_boxed_616_; uint8_t v_kind_boxed_617_; lean_object* v_res_618_; 
v_nondep_boxed_616_ = lean_unbox(v_nondep_608_);
v_kind_boxed_617_ = lean_unbox(v_kind_609_);
v_res_618_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_604_, v_type_605_, v_val_606_, v_k_607_, v_nondep_boxed_616_, v_kind_boxed_617_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(lean_object* v_name_619_, uint8_t v_bi_620_, lean_object* v_type_621_, lean_object* v_k_622_, uint8_t v_kind_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___f_630_; lean_object* v___x_631_; 
lean_inc(v___y_624_);
v___f_630_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_630_, 0, v_k_622_);
lean_closure_set(v___f_630_, 1, v___y_624_);
v___x_631_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_619_, v_bi_620_, v_type_621_, v___f_630_, v_kind_623_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_631_) == 0)
{
return v___x_631_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg___boxed(lean_object* v_name_640_, lean_object* v_bi_641_, lean_object* v_type_642_, lean_object* v_k_643_, lean_object* v_kind_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
uint8_t v_bi_boxed_651_; uint8_t v_kind_boxed_652_; lean_object* v_res_653_; 
v_bi_boxed_651_ = lean_unbox(v_bi_641_);
v_kind_boxed_652_ = lean_unbox(v_kind_644_);
v_res_653_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_640_, v_bi_boxed_651_, v_type_642_, v_k_643_, v_kind_boxed_652_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_object* v_00_u03b1_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_apply_1(v_x_655_, lean_box(0));
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0___boxed(lean_object* v_00_u03b1_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(v_00_u03b1_663_, v_x_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(lean_object* v_a_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_672_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_box(0);
return v___x_673_;
}
else
{
lean_object* v_key_674_; lean_object* v_value_675_; lean_object* v_tail_676_; uint8_t v___x_677_; 
v_key_674_ = lean_ctor_get(v_x_672_, 0);
v_value_675_ = lean_ctor_get(v_x_672_, 1);
v_tail_676_ = lean_ctor_get(v_x_672_, 2);
v___x_677_ = l_Lean_ExprStructEq_beq(v_key_674_, v_a_671_);
if (v___x_677_ == 0)
{
v_x_672_ = v_tail_676_;
goto _start;
}
else
{
lean_object* v___x_679_; 
lean_inc(v_value_675_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v_value_675_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg___boxed(lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_680_, v_x_681_);
lean_dec(v_x_681_);
lean_dec_ref(v_a_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(lean_object* v_m_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_buckets_685_; lean_object* v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v_fold_690_; uint64_t v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_buckets_685_ = lean_ctor_get(v_m_683_, 1);
v___x_686_ = lean_array_get_size(v_buckets_685_);
v___x_687_ = l_Lean_ExprStructEq_hash(v_a_684_);
v___x_688_ = 32ULL;
v___x_689_ = lean_uint64_shift_right(v___x_687_, v___x_688_);
v_fold_690_ = lean_uint64_xor(v___x_687_, v___x_689_);
v___x_691_ = 16ULL;
v___x_692_ = lean_uint64_shift_right(v_fold_690_, v___x_691_);
v___x_693_ = lean_uint64_xor(v_fold_690_, v___x_692_);
v___x_694_ = lean_uint64_to_usize(v___x_693_);
v___x_695_ = lean_usize_of_nat(v___x_686_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_sub(v___x_695_, v___x_696_);
v___x_698_ = lean_usize_land(v___x_694_, v___x_697_);
v___x_699_ = lean_array_uget_borrowed(v_buckets_685_, v___x_698_);
v___x_700_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_684_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_m_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_701_, v_a_702_);
lean_dec_ref(v_a_702_);
lean_dec_ref(v_m_701_);
return v_res_703_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(lean_object* v_a_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
uint8_t v___x_706_; 
v___x_706_ = 0;
return v___x_706_;
}
else
{
lean_object* v_key_707_; lean_object* v_tail_708_; uint8_t v___x_709_; 
v_key_707_ = lean_ctor_get(v_x_705_, 0);
v_tail_708_ = lean_ctor_get(v_x_705_, 2);
v___x_709_ = l_Lean_ExprStructEq_beq(v_key_707_, v_a_704_);
if (v___x_709_ == 0)
{
v_x_705_ = v_tail_708_;
goto _start;
}
else
{
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg___boxed(lean_object* v_a_711_, lean_object* v_x_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_711_, v_x_712_);
lean_dec(v_x_712_);
lean_dec_ref(v_a_711_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 0)
{
return v_x_715_;
}
else
{
lean_object* v_key_717_; lean_object* v_value_718_; lean_object* v_tail_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_742_; 
v_key_717_ = lean_ctor_get(v_x_716_, 0);
v_value_718_ = lean_ctor_get(v_x_716_, 1);
v_tail_719_ = lean_ctor_get(v_x_716_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_716_);
if (v_isSharedCheck_742_ == 0)
{
v___x_721_ = v_x_716_;
v_isShared_722_ = v_isSharedCheck_742_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_tail_719_);
lean_inc(v_value_718_);
lean_inc(v_key_717_);
lean_dec(v_x_716_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_742_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v_fold_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_723_ = lean_array_get_size(v_x_715_);
v___x_724_ = l_Lean_ExprStructEq_hash(v_key_717_);
v___x_725_ = 32ULL;
v___x_726_ = lean_uint64_shift_right(v___x_724_, v___x_725_);
v_fold_727_ = lean_uint64_xor(v___x_724_, v___x_726_);
v___x_728_ = 16ULL;
v___x_729_ = lean_uint64_shift_right(v_fold_727_, v___x_728_);
v___x_730_ = lean_uint64_xor(v_fold_727_, v___x_729_);
v___x_731_ = lean_uint64_to_usize(v___x_730_);
v___x_732_ = lean_usize_of_nat(v___x_723_);
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_sub(v___x_732_, v___x_733_);
v___x_735_ = lean_usize_land(v___x_731_, v___x_734_);
v___x_736_ = lean_array_uget_borrowed(v_x_715_, v___x_735_);
lean_inc(v___x_736_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 2, v___x_736_);
v___x_738_ = v___x_721_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_key_717_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_value_718_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v___x_736_);
v___x_738_ = v_reuseFailAlloc_741_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_array_uset(v_x_715_, v___x_735_, v___x_738_);
v_x_715_ = v___x_739_;
v_x_716_ = v_tail_719_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(lean_object* v_i_743_, lean_object* v_source_744_, lean_object* v_target_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_source_744_);
v___x_747_ = lean_nat_dec_lt(v_i_743_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec_ref(v_source_744_);
lean_dec(v_i_743_);
return v_target_745_;
}
else
{
lean_object* v_es_748_; lean_object* v___x_749_; lean_object* v_source_750_; lean_object* v_target_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_es_748_ = lean_array_fget(v_source_744_, v_i_743_);
v___x_749_ = lean_box(0);
v_source_750_ = lean_array_fset(v_source_744_, v_i_743_, v___x_749_);
v_target_751_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_target_745_, v_es_748_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_i_743_, v___x_752_);
lean_dec(v_i_743_);
v_i_743_ = v___x_753_;
v_source_744_ = v_source_750_;
v_target_745_ = v_target_751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(lean_object* v_data_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_nbuckets_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_756_ = lean_array_get_size(v_data_755_);
v___x_757_ = lean_unsigned_to_nat(2u);
v_nbuckets_758_ = lean_nat_mul(v___x_756_, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_box(0);
v___x_761_ = lean_mk_array(v_nbuckets_758_, v___x_760_);
v___x_762_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v___x_759_, v_data_755_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(lean_object* v_a_763_, lean_object* v_b_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_dec(v_b_764_);
lean_dec_ref(v_a_763_);
return v_x_765_;
}
else
{
lean_object* v_key_766_; lean_object* v_value_767_; lean_object* v_tail_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_780_; 
v_key_766_ = lean_ctor_get(v_x_765_, 0);
v_value_767_ = lean_ctor_get(v_x_765_, 1);
v_tail_768_ = lean_ctor_get(v_x_765_, 2);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_780_ == 0)
{
v___x_770_ = v_x_765_;
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_tail_768_);
lean_inc(v_value_767_);
lean_inc(v_key_766_);
lean_dec(v_x_765_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
uint8_t v___x_772_; 
v___x_772_ = l_Lean_ExprStructEq_beq(v_key_766_, v_a_763_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_763_, v_b_764_, v_tail_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 2, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_key_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_value_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v_value_767_);
lean_dec(v_key_766_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_b_764_);
lean_ctor_set(v___x_770_, 0, v_a_763_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_763_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_b_764_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_tail_768_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(lean_object* v_m_781_, lean_object* v_a_782_, lean_object* v_b_783_){
_start:
{
lean_object* v_size_784_; lean_object* v_buckets_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_828_; 
v_size_784_ = lean_ctor_get(v_m_781_, 0);
v_buckets_785_ = lean_ctor_get(v_m_781_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_m_781_);
if (v_isSharedCheck_828_ == 0)
{
v___x_787_ = v_m_781_;
v_isShared_788_ = v_isSharedCheck_828_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_buckets_785_);
lean_inc(v_size_784_);
lean_dec(v_m_781_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_828_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v_fold_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v_bkt_802_; uint8_t v___x_803_; 
v___x_789_ = lean_array_get_size(v_buckets_785_);
v___x_790_ = l_Lean_ExprStructEq_hash(v_a_782_);
v___x_791_ = 32ULL;
v___x_792_ = lean_uint64_shift_right(v___x_790_, v___x_791_);
v_fold_793_ = lean_uint64_xor(v___x_790_, v___x_792_);
v___x_794_ = 16ULL;
v___x_795_ = lean_uint64_shift_right(v_fold_793_, v___x_794_);
v___x_796_ = lean_uint64_xor(v_fold_793_, v___x_795_);
v___x_797_ = lean_uint64_to_usize(v___x_796_);
v___x_798_ = lean_usize_of_nat(v___x_789_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_sub(v___x_798_, v___x_799_);
v___x_801_ = lean_usize_land(v___x_797_, v___x_800_);
v_bkt_802_ = lean_array_uget_borrowed(v_buckets_785_, v___x_801_);
v___x_803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_782_, v_bkt_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v_size_x27_805_; lean_object* v___x_806_; lean_object* v_buckets_x27_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_804_ = lean_unsigned_to_nat(1u);
v_size_x27_805_ = lean_nat_add(v_size_784_, v___x_804_);
lean_dec(v_size_784_);
lean_inc(v_bkt_802_);
v___x_806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_806_, 0, v_a_782_);
lean_ctor_set(v___x_806_, 1, v_b_783_);
lean_ctor_set(v___x_806_, 2, v_bkt_802_);
v_buckets_x27_807_ = lean_array_uset(v_buckets_785_, v___x_801_, v___x_806_);
v___x_808_ = lean_unsigned_to_nat(4u);
v___x_809_ = lean_nat_mul(v_size_x27_805_, v___x_808_);
v___x_810_ = lean_unsigned_to_nat(3u);
v___x_811_ = lean_nat_div(v___x_809_, v___x_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_array_get_size(v_buckets_x27_807_);
v___x_813_ = lean_nat_dec_le(v___x_811_, v___x_812_);
lean_dec(v___x_811_);
if (v___x_813_ == 0)
{
lean_object* v_val_814_; lean_object* v___x_816_; 
v_val_814_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_buckets_x27_807_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_val_814_);
lean_ctor_set(v___x_787_, 0, v_size_x27_805_);
v___x_816_ = v___x_787_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_size_x27_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_val_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___x_819_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_buckets_x27_807_);
lean_ctor_set(v___x_787_, 0, v_size_x27_805_);
v___x_819_ = v___x_787_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_size_x27_805_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_buckets_x27_807_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v___x_821_; lean_object* v_buckets_x27_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_bkt_802_);
v___x_821_ = lean_box(0);
v_buckets_x27_822_ = lean_array_uset(v_buckets_785_, v___x_801_, v___x_821_);
v___x_823_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_782_, v_b_783_, v_bkt_802_);
v___x_824_ = lean_array_uset(v_buckets_x27_822_, v___x_801_, v___x_823_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_824_);
v___x_826_ = v___x_787_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_size_784_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(lean_object* v_a_829_, lean_object* v_e_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_st_ref_take(v_a_829_);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v___x_833_, v_e_830_, v_a_831_);
v___x_835_ = lean_st_ref_set(v_a_829_, v___x_834_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed(lean_object* v_a_837_, lean_object* v_e_838_, lean_object* v_a_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2(v_a_837_, v_e_838_, v_a_839_);
lean_dec(v_a_837_);
return v_res_841_;
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
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
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
lean_dec_ref(v_e_884_);
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_e_896_ = lean_ctor_get(v_a_892_, 0);
lean_inc_ref(v_e_896_);
lean_dec_ref_known(v_a_892_, 1);
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
lean_dec_ref_known(v_a_892_, 1);
v___x_901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_879_, v_post_880_, v_usedLetOnly_881_, v_skipConstInApp_882_, v_skipInstances_883_, v_e_900_, v_a_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_901_;
}
default: 
{
lean_object* v_e_x3f_902_; 
lean_dec_ref(v_post_880_);
lean_dec_ref(v_pre_879_);
v_e_x3f_902_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_e_x3f_902_);
lean_dec_ref_known(v_a_892_, 1);
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
lean_dec_ref_known(v_e_x3f_902_, 1);
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
lean_dec_ref_known(v_e_925_, 3);
v___x_936_ = lean_expr_instantiate_rev(v_binderType_933_, v_fvars_924_);
lean_dec_ref(v_binderType_933_);
lean_inc_ref(v_post_920_);
lean_inc_ref(v_pre_919_);
v___x_937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_919_, v_post_920_, v_usedLetOnly_921_, v_skipConstInApp_922_, v_skipInstances_923_, v___x_936_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___f_942_; uint8_t v___x_943_; lean_object* v___x_944_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
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
lean_inc_ref(v_post_920_);
lean_inc_ref(v_pre_919_);
v___x_946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_919_, v_post_920_, v_usedLetOnly_921_, v_skipConstInApp_922_, v_skipInstances_923_, v___x_945_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
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
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_919_, v_post_920_, v_usedLetOnly_921_, v_skipConstInApp_922_, v_skipInstances_923_, v_a_952_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_953_;
}
else
{
lean_dec_ref(v_post_920_);
lean_dec_ref(v_pre_919_);
return v___x_951_;
}
}
else
{
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
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
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
lean_dec_ref_known(v_e_994_, 4);
v___x_1006_ = lean_expr_instantiate_rev(v_type_1002_, v_fvars_993_);
lean_dec_ref(v_type_1002_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1006_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_expr_instantiate_rev(v_value_1003_, v_fvars_993_);
lean_dec_ref(v_value_1003_);
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1009_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
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
lean_inc_ref(v_post_989_);
lean_inc_ref(v_pre_988_);
v___x_1019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v___x_1018_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; uint8_t v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = 0;
v___x_1022_ = 1;
v___x_1023_ = l_Lean_Meta_mkLetFVars(v_fvars_993_, v_a_1020_, v_usedLetOnly_990_, v___x_1021_, v___x_1022_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec_ref(v_fvars_993_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_988_, v_post_989_, v_usedLetOnly_990_, v_skipConstInApp_991_, v_skipInstances_992_, v_a_1024_, v_a_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1025_;
}
else
{
lean_dec_ref(v_post_989_);
lean_dec_ref(v_pre_988_);
return v___x_1023_;
}
}
else
{
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
lean_inc(v_v_1042_);
lean_inc_ref(v_post_1027_);
lean_inc_ref(v_pre_1026_);
v___x_1043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1026_, v_post_1027_, v_usedLetOnly_1028_, v_skipConstInApp_1029_, v_skipInstances_1030_, v_v_1042_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v_bs_x27_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
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
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v_a_1100_);
lean_dec(v___y_1098_);
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
lean_dec(v_a_1117_);
lean_dec_ref(v_post_1113_);
lean_dec_ref(v_pre_1112_);
v_a_1132_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v_a_1128_, 1);
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
lean_dec_ref_known(v_a_1128_, 1);
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
lean_dec_ref_known(v_x_1171_, 2);
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
lean_inc_ref(v_post_1168_);
lean_inc_ref(v_pre_1167_);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v_sz_1187_, v___x_1188_, v_x_1172_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = l_Lean_mkAppN(v_f_1181_, v_a_1190_);
lean_dec(v_a_1190_);
v___x_1192_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v___x_1191_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
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
lean_inc_ref(v_f_1181_);
v___x_1202_ = l_Lean_Meta_getFunInfoNArgs(v_f_1181_, v___x_1201_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_paramInfo_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_paramInfo_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc_ref(v_paramInfo_1204_);
lean_dec(v_a_1203_);
v___x_1205_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1168_);
lean_inc_ref(v_pre_1167_);
v___x_1206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v___x_1201_, v_paramInfo_1204_, v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v___x_1205_, v_x_1172_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec_ref(v_paramInfo_1204_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = l_Lean_mkAppN(v_f_1181_, v_a_1207_);
lean_dec(v_a_1207_);
v___x_1209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v___x_1208_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1209_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
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
lean_inc_ref(v_post_1168_);
lean_inc_ref(v_pre_1167_);
v___x_1227_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1167_, v_post_1168_, v_usedLetOnly_1169_, v_skipConstInApp_1170_, v_skipInstances_1166_, v_x_1171_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
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
lean_dec_ref(v_x_1172_);
lean_dec_ref(v_post_1168_);
lean_dec_ref(v_pre_1167_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(lean_object* v___x_1236_, lean_object* v_pre_1237_, lean_object* v_e_1238_, lean_object* v_post_1239_, uint8_t v_usedLetOnly_1240_, uint8_t v_skipConstInApp_1241_, uint8_t v_skipInstances_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Core_checkSystem(v___x_1236_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref_known(v___x_1249_, 1);
lean_inc_ref(v_pre_1237_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc_ref(v_e_1238_);
v___x_1250_ = lean_apply_6(v_pre_1237_, v_e_1238_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, lean_box(0));
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1299_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1299_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1299_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___y_1256_; 
switch(lean_obj_tag(v_a_1251_))
{
case 0:
{
lean_object* v_e_1291_; lean_object* v___x_1293_; 
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_e_1238_);
lean_dec_ref(v_pre_1237_);
v_e_1291_ = lean_ctor_get(v_a_1251_, 0);
lean_inc_ref(v_e_1291_);
lean_dec_ref_known(v_a_1251_, 1);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v_e_1291_);
v___x_1293_ = v___x_1253_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_e_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
case 1:
{
lean_object* v_e_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1253_);
lean_dec_ref(v_e_1238_);
v_e_1295_ = lean_ctor_get(v_a_1251_, 0);
lean_inc_ref(v_e_1295_);
lean_dec_ref_known(v_a_1251_, 1);
v___x_1296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v_e_1295_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1296_;
}
default: 
{
lean_object* v_e_x3f_1297_; 
lean_del_object(v___x_1253_);
v_e_x3f_1297_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_e_x3f_1297_);
lean_dec_ref_known(v_a_1251_, 1);
if (lean_obj_tag(v_e_x3f_1297_) == 0)
{
v___y_1256_ = v_e_1238_;
goto v___jp_1255_;
}
else
{
lean_object* v_val_1298_; 
lean_dec_ref(v_e_1238_);
v_val_1298_ = lean_ctor_get(v_e_x3f_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_e_x3f_1297_, 1);
v___y_1256_ = v_val_1298_;
goto v___jp_1255_;
}
}
}
v___jp_1255_:
{
switch(lean_obj_tag(v___y_1256_))
{
case 7:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1257_, v___y_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1258_;
}
case 6:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1259_, v___y_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1260_;
}
case 8:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___closed__0));
v___x_1262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1261_, v___y_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1262_;
}
case 5:
{
lean_object* v_dummy_1263_; lean_object* v_nargs_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_dummy_1263_ = lean_obj_once(&l_Lean_Elab_WF_withAppN___closed__0, &l_Lean_Elab_WF_withAppN___closed__0_once, _init_l_Lean_Elab_WF_withAppN___closed__0);
v_nargs_1264_ = l_Lean_Expr_getAppNumArgs(v___y_1256_);
lean_inc(v_nargs_1264_);
v___x_1265_ = lean_mk_array(v_nargs_1264_, v_dummy_1263_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_sub(v_nargs_1264_, v___x_1266_);
lean_dec(v_nargs_1264_);
v___x_1268_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_1242_, v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v___y_1256_, v___x_1265_, v___x_1267_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1268_;
}
case 10:
{
lean_object* v_data_1269_; lean_object* v_expr_1270_; lean_object* v___x_1271_; 
v_data_1269_ = lean_ctor_get(v___y_1256_, 0);
v_expr_1270_ = lean_ctor_get(v___y_1256_, 1);
lean_inc_ref(v_expr_1270_);
lean_inc_ref(v_post_1239_);
lean_inc_ref(v_pre_1237_);
v___x_1271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v_expr_1270_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; size_t v___x_1273_; size_t v___x_1274_; uint8_t v___x_1275_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = lean_ptr_addr(v_expr_1270_);
v___x_1274_ = lean_ptr_addr(v_a_1272_);
v___x_1275_ = lean_usize_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v_data_1269_);
lean_dec_ref_known(v___y_1256_, 2);
v___x_1276_ = l_Lean_Expr_mdata___override(v_data_1269_, v_a_1272_);
v___x_1277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1276_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; 
lean_dec(v_a_1272_);
v___x_1278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___y_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1278_;
}
}
else
{
lean_dec_ref_known(v___y_1256_, 2);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1237_);
return v___x_1271_;
}
}
case 11:
{
lean_object* v_typeName_1279_; lean_object* v_idx_1280_; lean_object* v_struct_1281_; lean_object* v___x_1282_; 
v_typeName_1279_ = lean_ctor_get(v___y_1256_, 0);
v_idx_1280_ = lean_ctor_get(v___y_1256_, 1);
v_struct_1281_ = lean_ctor_get(v___y_1256_, 2);
lean_inc_ref(v_struct_1281_);
lean_inc_ref(v_post_1239_);
lean_inc_ref(v_pre_1237_);
v___x_1282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v_struct_1281_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; size_t v___x_1284_; size_t v___x_1285_; uint8_t v___x_1286_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = lean_ptr_addr(v_struct_1281_);
v___x_1285_ = lean_ptr_addr(v_a_1283_);
v___x_1286_ = lean_usize_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_inc(v_idx_1280_);
lean_inc(v_typeName_1279_);
lean_dec_ref_known(v___y_1256_, 3);
v___x_1287_ = l_Lean_Expr_proj___override(v_typeName_1279_, v_idx_1280_, v_a_1283_);
v___x_1288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___x_1287_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; 
lean_dec(v_a_1283_);
v___x_1289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___y_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1289_;
}
}
else
{
lean_dec_ref_known(v___y_1256_, 3);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1237_);
return v___x_1282_;
}
}
default: 
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1237_, v_post_1239_, v_usedLetOnly_1240_, v_skipConstInApp_1241_, v_skipInstances_1242_, v___y_1256_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_e_1238_);
lean_dec_ref(v_pre_1237_);
v_a_1300_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1250_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1250_);
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
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_e_1238_);
lean_dec_ref(v_pre_1237_);
v_a_1308_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1249_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1249_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed(lean_object* v___x_1316_, lean_object* v_pre_1317_, lean_object* v_e_1318_, lean_object* v_post_1319_, lean_object* v_usedLetOnly_1320_, lean_object* v_skipConstInApp_1321_, lean_object* v_skipInstances_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v_usedLetOnly_boxed_1329_; uint8_t v_skipConstInApp_boxed_1330_; uint8_t v_skipInstances_boxed_1331_; lean_object* v_res_1332_; 
v_usedLetOnly_boxed_1329_ = lean_unbox(v_usedLetOnly_1320_);
v_skipConstInApp_boxed_1330_ = lean_unbox(v_skipConstInApp_1321_);
v_skipInstances_boxed_1331_ = lean_unbox(v_skipInstances_1322_);
v_res_1332_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1(v___x_1316_, v_pre_1317_, v_e_1318_, v_post_1319_, v_usedLetOnly_boxed_1329_, v_skipConstInApp_boxed_1330_, v_skipInstances_boxed_1331_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(lean_object* v_pre_1333_, lean_object* v_post_1334_, uint8_t v_usedLetOnly_1335_, uint8_t v_skipConstInApp_1336_, uint8_t v_skipInstances_1337_, lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_inc(v_a_1339_);
v___x_1345_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1345_, 0, lean_box(0));
lean_closure_set(v___x_1345_, 1, lean_box(0));
lean_closure_set(v___x_1345_, 2, v_a_1339_);
v___x_1346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___x_1345_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1381_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1381_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1381_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_a_1347_, v_e_1338_);
lean_dec(v_a_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; 
lean_del_object(v___x_1349_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___closed__0));
v___x_1353_ = lean_box(v_usedLetOnly_1335_);
v___x_1354_ = lean_box(v_skipConstInApp_1336_);
v___x_1355_ = lean_box(v_skipInstances_1337_);
lean_inc_ref(v_e_1338_);
v___f_1356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1356_, 0, v___x_1352_);
lean_closure_set(v___f_1356_, 1, v_pre_1333_);
lean_closure_set(v___f_1356_, 2, v_e_1338_);
lean_closure_set(v___f_1356_, 3, v_post_1334_);
lean_closure_set(v___f_1356_, 4, v___x_1353_);
lean_closure_set(v___f_1356_, 5, v___x_1354_);
lean_closure_set(v___f_1356_, 6, v___x_1355_);
v___x_1357_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v___f_1356_, v_a_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc_n(v_a_1358_, 2);
lean_dec_ref_known(v___x_1357_, 1);
lean_inc(v_a_1339_);
v___f_1359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1359_, 0, v_a_1339_);
lean_closure_set(v___f_1359_, 1, v_e_1338_);
lean_closure_set(v___f_1359_, 2, v_a_1358_);
v___x_1360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___lam__0(lean_box(0), v___f_1359_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1360_, 0);
lean_dec(v_unused_1368_);
v___x_1362_ = v___x_1360_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v___x_1360_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_a_1358_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1358_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_a_1358_);
v_a_1369_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1360_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1360_);
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
lean_dec_ref(v_e_1338_);
return v___x_1357_;
}
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1379_; 
lean_dec_ref(v_e_1338_);
lean_dec_ref(v_post_1334_);
lean_dec_ref(v_pre_1333_);
v_val_1377_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1351_, 1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_val_1377_);
v___x_1379_ = v___x_1349_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_val_1377_);
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
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_e_1338_);
lean_dec_ref(v_post_1334_);
lean_dec_ref(v_pre_1333_);
v_a_1382_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1346_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1346_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_1390_, lean_object* v_pre_1391_, lean_object* v_post_1392_, lean_object* v_usedLetOnly_1393_, lean_object* v_skipConstInApp_1394_, lean_object* v_skipInstances_1395_, lean_object* v_body_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_usedLetOnly_boxed_1404_; uint8_t v_skipConstInApp_boxed_1405_; uint8_t v_skipInstances_boxed_1406_; lean_object* v_res_1407_; 
v_usedLetOnly_boxed_1404_ = lean_unbox(v_usedLetOnly_1393_);
v_skipConstInApp_boxed_1405_ = lean_unbox(v_skipConstInApp_1394_);
v_skipInstances_boxed_1406_ = lean_unbox(v_skipInstances_1395_);
v_res_1407_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(v_fvars_1390_, v_pre_1391_, v_post_1392_, v_usedLetOnly_boxed_1404_, v_skipConstInApp_boxed_1405_, v_skipInstances_boxed_1406_, v_body_1396_, v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(lean_object* v_pre_1408_, lean_object* v_post_1409_, uint8_t v_usedLetOnly_1410_, uint8_t v_skipConstInApp_1411_, uint8_t v_skipInstances_1412_, lean_object* v_fvars_1413_, lean_object* v_e_1414_, lean_object* v_a_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
if (lean_obj_tag(v_e_1414_) == 7)
{
lean_object* v_binderName_1421_; lean_object* v_binderType_1422_; lean_object* v_body_1423_; uint8_t v_binderInfo_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_binderName_1421_ = lean_ctor_get(v_e_1414_, 0);
lean_inc(v_binderName_1421_);
v_binderType_1422_ = lean_ctor_get(v_e_1414_, 1);
lean_inc_ref(v_binderType_1422_);
v_body_1423_ = lean_ctor_get(v_e_1414_, 2);
lean_inc_ref(v_body_1423_);
v_binderInfo_1424_ = lean_ctor_get_uint8(v_e_1414_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1414_, 3);
v___x_1425_ = lean_expr_instantiate_rev(v_binderType_1422_, v_fvars_1413_);
lean_dec_ref(v_binderType_1422_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1408_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1408_, v_post_1409_, v_usedLetOnly_1410_, v_skipConstInApp_1411_, v_skipInstances_1412_, v___x_1425_, v_a_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = lean_box(v_usedLetOnly_1410_);
v___x_1429_ = lean_box(v_skipConstInApp_1411_);
v___x_1430_ = lean_box(v_skipInstances_1412_);
v___f_1431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1431_, 0, v_fvars_1413_);
lean_closure_set(v___f_1431_, 1, v_pre_1408_);
lean_closure_set(v___f_1431_, 2, v_post_1409_);
lean_closure_set(v___f_1431_, 3, v___x_1428_);
lean_closure_set(v___f_1431_, 4, v___x_1429_);
lean_closure_set(v___f_1431_, 5, v___x_1430_);
lean_closure_set(v___f_1431_, 6, v_body_1423_);
v___x_1432_ = 0;
v___x_1433_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_binderName_1421_, v_binderInfo_1424_, v_a_1427_, v___f_1431_, v___x_1432_, v_a_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1433_;
}
else
{
lean_dec_ref(v_body_1423_);
lean_dec(v_binderName_1421_);
lean_dec_ref(v_fvars_1413_);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1408_);
return v___x_1426_;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_expr_instantiate_rev(v_e_1414_, v_fvars_1413_);
lean_dec_ref(v_e_1414_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1408_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1408_, v_post_1409_, v_usedLetOnly_1410_, v_skipConstInApp_1411_, v_skipInstances_1412_, v___x_1434_, v_a_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; uint8_t v___x_1437_; uint8_t v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = 0;
v___x_1438_ = 1;
v___x_1439_ = 1;
v___x_1440_ = l_Lean_Meta_mkForallFVars(v_fvars_1413_, v_a_1436_, v___x_1437_, v_usedLetOnly_1410_, v___x_1438_, v___x_1439_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec_ref(v_fvars_1413_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1408_, v_post_1409_, v_usedLetOnly_1410_, v_skipConstInApp_1411_, v_skipInstances_1412_, v_a_1441_, v_a_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1442_;
}
else
{
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1408_);
return v___x_1440_;
}
}
else
{
lean_dec_ref(v_fvars_1413_);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1408_);
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___lam__0(lean_object* v_fvars_1443_, lean_object* v_pre_1444_, lean_object* v_post_1445_, uint8_t v_usedLetOnly_1446_, uint8_t v_skipConstInApp_1447_, uint8_t v_skipInstances_1448_, lean_object* v_body_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_array_push(v_fvars_1443_, v_x_1450_);
v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1444_, v_post_1445_, v_usedLetOnly_1446_, v_skipConstInApp_1447_, v_skipInstances_1448_, v___x_1457_, v_body_1449_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7___boxed(lean_object* v_pre_1459_, lean_object* v_post_1460_, lean_object* v_usedLetOnly_1461_, lean_object* v_skipConstInApp_1462_, lean_object* v_skipInstances_1463_, lean_object* v_e_1464_, lean_object* v_a_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_usedLetOnly_boxed_1471_; uint8_t v_skipConstInApp_boxed_1472_; uint8_t v_skipInstances_boxed_1473_; lean_object* v_res_1474_; 
v_usedLetOnly_boxed_1471_ = lean_unbox(v_usedLetOnly_1461_);
v_skipConstInApp_boxed_1472_ = lean_unbox(v_skipConstInApp_1462_);
v_skipInstances_boxed_1473_ = lean_unbox(v_skipInstances_1463_);
v_res_1474_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__7(v_pre_1459_, v_post_1460_, v_usedLetOnly_boxed_1471_, v_skipConstInApp_boxed_1472_, v_skipInstances_boxed_1473_, v_e_1464_, v_a_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v_a_1465_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6___boxed(lean_object* v_pre_1475_, lean_object* v_post_1476_, lean_object* v_usedLetOnly_1477_, lean_object* v_skipConstInApp_1478_, lean_object* v_skipInstances_1479_, lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_bs_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v_usedLetOnly_boxed_1489_; uint8_t v_skipConstInApp_boxed_1490_; uint8_t v_skipInstances_boxed_1491_; size_t v_sz_boxed_1492_; size_t v_i_boxed_1493_; lean_object* v_res_1494_; 
v_usedLetOnly_boxed_1489_ = lean_unbox(v_usedLetOnly_1477_);
v_skipConstInApp_boxed_1490_ = lean_unbox(v_skipConstInApp_1478_);
v_skipInstances_boxed_1491_ = lean_unbox(v_skipInstances_1479_);
v_sz_boxed_1492_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1493_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__6(v_pre_1475_, v_post_1476_, v_usedLetOnly_boxed_1489_, v_skipConstInApp_boxed_1490_, v_skipInstances_boxed_1491_, v_sz_boxed_1492_, v_i_boxed_1493_, v_bs_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4___boxed(lean_object* v_pre_1495_, lean_object* v_post_1496_, lean_object* v_usedLetOnly_1497_, lean_object* v_skipConstInApp_1498_, lean_object* v_skipInstances_1499_, lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v_usedLetOnly_boxed_1507_; uint8_t v_skipConstInApp_boxed_1508_; uint8_t v_skipInstances_boxed_1509_; lean_object* v_res_1510_; 
v_usedLetOnly_boxed_1507_ = lean_unbox(v_usedLetOnly_1497_);
v_skipConstInApp_boxed_1508_ = lean_unbox(v_skipConstInApp_1498_);
v_skipInstances_boxed_1509_ = lean_unbox(v_skipInstances_1499_);
v_res_1510_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1495_, v_post_1496_, v_usedLetOnly_boxed_1507_, v_skipConstInApp_boxed_1508_, v_skipInstances_boxed_1509_, v_e_1500_, v_a_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v_a_1501_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10___boxed(lean_object* v_pre_1511_, lean_object* v_post_1512_, lean_object* v_usedLetOnly_1513_, lean_object* v_skipConstInApp_1514_, lean_object* v_skipInstances_1515_, lean_object* v_fvars_1516_, lean_object* v_e_1517_, lean_object* v_a_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_usedLetOnly_boxed_1524_; uint8_t v_skipConstInApp_boxed_1525_; uint8_t v_skipInstances_boxed_1526_; lean_object* v_res_1527_; 
v_usedLetOnly_boxed_1524_ = lean_unbox(v_usedLetOnly_1513_);
v_skipConstInApp_boxed_1525_ = lean_unbox(v_skipConstInApp_1514_);
v_skipInstances_boxed_1526_ = lean_unbox(v_skipInstances_1515_);
v_res_1527_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10(v_pre_1511_, v_post_1512_, v_usedLetOnly_boxed_1524_, v_skipConstInApp_boxed_1525_, v_skipInstances_boxed_1526_, v_fvars_1516_, v_e_1517_, v_a_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v_a_1518_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11___boxed(lean_object* v_pre_1528_, lean_object* v_post_1529_, lean_object* v_usedLetOnly_1530_, lean_object* v_skipConstInApp_1531_, lean_object* v_skipInstances_1532_, lean_object* v_fvars_1533_, lean_object* v_e_1534_, lean_object* v_a_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v_usedLetOnly_boxed_1541_; uint8_t v_skipConstInApp_boxed_1542_; uint8_t v_skipInstances_boxed_1543_; lean_object* v_res_1544_; 
v_usedLetOnly_boxed_1541_ = lean_unbox(v_usedLetOnly_1530_);
v_skipConstInApp_boxed_1542_ = lean_unbox(v_skipConstInApp_1531_);
v_skipInstances_boxed_1543_ = lean_unbox(v_skipInstances_1532_);
v_res_1544_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__11(v_pre_1528_, v_post_1529_, v_usedLetOnly_boxed_1541_, v_skipConstInApp_boxed_1542_, v_skipInstances_boxed_1543_, v_fvars_1533_, v_e_1534_, v_a_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_a_1535_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12___boxed(lean_object* v_pre_1545_, lean_object* v_post_1546_, lean_object* v_usedLetOnly_1547_, lean_object* v_skipConstInApp_1548_, lean_object* v_skipInstances_1549_, lean_object* v_fvars_1550_, lean_object* v_e_1551_, lean_object* v_a_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_usedLetOnly_boxed_1558_; uint8_t v_skipConstInApp_boxed_1559_; uint8_t v_skipInstances_boxed_1560_; lean_object* v_res_1561_; 
v_usedLetOnly_boxed_1558_ = lean_unbox(v_usedLetOnly_1547_);
v_skipConstInApp_boxed_1559_ = lean_unbox(v_skipConstInApp_1548_);
v_skipInstances_boxed_1560_ = lean_unbox(v_skipInstances_1549_);
v_res_1561_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12(v_pre_1545_, v_post_1546_, v_usedLetOnly_boxed_1558_, v_skipConstInApp_boxed_1559_, v_skipInstances_boxed_1560_, v_fvars_1550_, v_e_1551_, v_a_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v_a_1552_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_upperBound_1562_, lean_object* v___x_1563_, lean_object* v_pre_1564_, lean_object* v_post_1565_, lean_object* v_usedLetOnly_1566_, lean_object* v_skipConstInApp_1567_, lean_object* v_skipInstances_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_usedLetOnly_boxed_1577_; uint8_t v_skipConstInApp_boxed_1578_; uint8_t v_skipInstances_boxed_1579_; lean_object* v_res_1580_; 
v_usedLetOnly_boxed_1577_ = lean_unbox(v_usedLetOnly_1566_);
v_skipConstInApp_boxed_1578_ = lean_unbox(v_skipConstInApp_1567_);
v_skipInstances_boxed_1579_ = lean_unbox(v_skipInstances_1568_);
v_res_1580_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1562_, v___x_1563_, v_pre_1564_, v_post_1565_, v_usedLetOnly_boxed_1577_, v_skipConstInApp_boxed_1578_, v_skipInstances_boxed_1579_, v_a_1569_, v_b_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___x_1563_);
lean_dec(v_upperBound_1562_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13___boxed(lean_object* v_skipInstances_1581_, lean_object* v_pre_1582_, lean_object* v_post_1583_, lean_object* v_usedLetOnly_1584_, lean_object* v_skipConstInApp_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v_skipInstances_boxed_1595_; uint8_t v_usedLetOnly_boxed_1596_; uint8_t v_skipConstInApp_boxed_1597_; lean_object* v_res_1598_; 
v_skipInstances_boxed_1595_ = lean_unbox(v_skipInstances_1581_);
v_usedLetOnly_boxed_1596_ = lean_unbox(v_usedLetOnly_1584_);
v_skipConstInApp_boxed_1597_ = lean_unbox(v_skipConstInApp_1585_);
v_res_1598_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__13(v_skipInstances_boxed_1595_, v_pre_1582_, v_post_1583_, v_usedLetOnly_boxed_1596_, v_skipConstInApp_boxed_1597_, v_x_1586_, v_x_1587_, v_x_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_unsigned_to_nat(16u);
v___x_1601_ = lean_mk_array(v___x_1600_, v___x_1599_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__0);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__1);
v___x_1606_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1606_, 0, lean_box(0));
lean_closure_set(v___x_1606_, 1, lean_box(0));
lean_closure_set(v___x_1606_, 2, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(lean_object* v_input_1607_, lean_object* v_pre_1608_, lean_object* v_post_1609_, uint8_t v_usedLetOnly_1610_, uint8_t v_skipConstInApp_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_a_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1617_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___closed__2);
v___x_1618_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1617_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = 0;
v___x_1621_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4(v_pre_1608_, v_post_1609_, v_usedLetOnly_1610_, v_skipConstInApp_1611_, v___x_1620_, v_input_1607_, v_a_1619_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1623_, 0, lean_box(0));
lean_closure_set(v___x_1623_, 1, lean_box(0));
lean_closure_set(v___x_1623_, 2, v_a_1619_);
v___x_1624_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___lam__0(lean_box(0), v___x_1623_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1632_);
v___x_1626_ = v___x_1624_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v___x_1624_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v_a_1622_);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1622_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_dec(v_a_1619_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3___boxed(lean_object* v_input_1633_, lean_object* v_pre_1634_, lean_object* v_post_1635_, lean_object* v_usedLetOnly_1636_, lean_object* v_skipConstInApp_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
uint8_t v_usedLetOnly_boxed_1643_; uint8_t v_skipConstInApp_boxed_1644_; lean_object* v_res_1645_; 
v_usedLetOnly_boxed_1643_ = lean_unbox(v_usedLetOnly_1636_);
v_skipConstInApp_boxed_1644_ = lean_unbox(v_skipConstInApp_1637_);
v_res_1645_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_input_1633_, v_pre_1634_, v_post_1635_, v_usedLetOnly_boxed_1643_, v_skipConstInApp_boxed_1644_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1645_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__2(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__1));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Elab_WF_packCalls___closed__4(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__3));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls(lean_object* v_fixedParamPerms_1653_, lean_object* v_argsPacker_1654_, lean_object* v_funNames_1655_, lean_object* v_newF_1656_, lean_object* v_e_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; 
lean_inc(v_a_1661_);
lean_inc_ref(v_a_1660_);
lean_inc(v_a_1659_);
lean_inc_ref(v_a_1658_);
lean_inc_ref(v_newF_1656_);
v___x_1663_ = lean_infer_type(v_newF_1656_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___f_1665_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; uint8_t v___x_1676_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___f_1665_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___closed__0));
v___x_1676_ = l_Lean_Expr_isForall(v_a_1664_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v_e_1657_);
lean_dec_ref(v_funNames_1655_);
lean_dec_ref(v_argsPacker_1654_);
lean_dec_ref(v_fixedParamPerms_1653_);
v___x_1677_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__2, &l_Lean_Elab_WF_packCalls___closed__2_once, _init_l_Lean_Elab_WF_packCalls___closed__2);
v___x_1678_ = l_Lean_MessageData_ofExpr(v_newF_1656_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___closed__4, &l_Lean_Elab_WF_packCalls___closed__4_once, _init_l_Lean_Elab_WF_packCalls___closed__4);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_MessageData_ofExpr(v_a_1664_);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0___redArg(v___x_1683_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
v___y_1667_ = v_a_1658_;
v___y_1668_ = v_a_1659_;
v___y_1669_ = v_a_1660_;
v___y_1670_ = v_a_1661_;
goto v___jp_1666_;
}
v___jp_1666_:
{
lean_object* v___x_1671_; lean_object* v___f_1672_; uint8_t v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1671_ = l_Lean_Expr_bindingDomain_x21(v_a_1664_);
lean_dec(v_a_1664_);
v___f_1672_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packCalls___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1672_, 0, v_funNames_1655_);
lean_closure_set(v___f_1672_, 1, v_fixedParamPerms_1653_);
lean_closure_set(v___f_1672_, 2, v_argsPacker_1654_);
lean_closure_set(v___f_1672_, 3, v___x_1671_);
lean_closure_set(v___f_1672_, 4, v_newF_1656_);
v___x_1673_ = 0;
v___x_1674_ = 1;
v___x_1675_ = l_Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3(v_e_1657_, v___f_1665_, v___f_1672_, v___x_1673_, v___x_1674_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1675_;
}
}
else
{
lean_dec_ref(v_e_1657_);
lean_dec_ref(v_newF_1656_);
lean_dec_ref(v_funNames_1655_);
lean_dec_ref(v_argsPacker_1654_);
lean_dec_ref(v_fixedParamPerms_1653_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packCalls___boxed(lean_object* v_fixedParamPerms_1693_, lean_object* v_argsPacker_1694_, lean_object* v_funNames_1695_, lean_object* v_newF_1696_, lean_object* v_e_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_1693_, v_argsPacker_1694_, v_funNames_1695_, v_newF_1696_, v_e_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(lean_object* v_upperBound_1704_, lean_object* v___x_1705_, lean_object* v_pre_1706_, lean_object* v_post_1707_, uint8_t v_usedLetOnly_1708_, uint8_t v_skipConstInApp_1709_, uint8_t v_skipInstances_1710_, lean_object* v___x_1711_, lean_object* v_inst_1712_, lean_object* v_R_1713_, lean_object* v_a_1714_, lean_object* v_b_1715_, lean_object* v_c_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___redArg(v_upperBound_1704_, v___x_1705_, v_pre_1706_, v_post_1707_, v_usedLetOnly_1708_, v_skipConstInApp_1709_, v_skipInstances_1710_, v_a_1714_, v_b_1715_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1724_ = _args[0];
lean_object* v___x_1725_ = _args[1];
lean_object* v_pre_1726_ = _args[2];
lean_object* v_post_1727_ = _args[3];
lean_object* v_usedLetOnly_1728_ = _args[4];
lean_object* v_skipConstInApp_1729_ = _args[5];
lean_object* v_skipInstances_1730_ = _args[6];
lean_object* v___x_1731_ = _args[7];
lean_object* v_inst_1732_ = _args[8];
lean_object* v_R_1733_ = _args[9];
lean_object* v_a_1734_ = _args[10];
lean_object* v_b_1735_ = _args[11];
lean_object* v_c_1736_ = _args[12];
lean_object* v___y_1737_ = _args[13];
lean_object* v___y_1738_ = _args[14];
lean_object* v___y_1739_ = _args[15];
lean_object* v___y_1740_ = _args[16];
lean_object* v___y_1741_ = _args[17];
lean_object* v___y_1742_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1743_; uint8_t v_skipConstInApp_boxed_1744_; uint8_t v_skipInstances_boxed_1745_; lean_object* v_res_1746_; 
v_usedLetOnly_boxed_1743_ = lean_unbox(v_usedLetOnly_1728_);
v_skipConstInApp_boxed_1744_ = lean_unbox(v_skipConstInApp_1729_);
v_skipInstances_boxed_1745_ = lean_unbox(v_skipInstances_1730_);
v_res_1746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__8(v_upperBound_1724_, v___x_1725_, v_pre_1726_, v_post_1727_, v_usedLetOnly_boxed_1743_, v_skipConstInApp_boxed_1744_, v_skipInstances_boxed_1745_, v___x_1731_, v_inst_1732_, v_R_1733_, v_a_1734_, v_b_1735_, v_c_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec(v___x_1731_);
lean_dec_ref(v___x_1725_);
lean_dec(v_upperBound_1724_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1747_, lean_object* v_m_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___redArg(v_m_1748_, v_a_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1751_, lean_object* v_m_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9(v_00_u03b2_1751_, v_m_1752_, v_a_1753_);
lean_dec_ref(v_a_1753_);
lean_dec_ref(v_m_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(lean_object* v_00_u03b1_1755_, lean_object* v_name_1756_, uint8_t v_bi_1757_, lean_object* v_type_1758_, lean_object* v_k_1759_, uint8_t v_kind_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___redArg(v_name_1756_, v_bi_1757_, v_type_1758_, v_k_1759_, v_kind_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_name_1769_, lean_object* v_bi_1770_, lean_object* v_type_1771_, lean_object* v_k_1772_, lean_object* v_kind_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v_bi_boxed_1780_; uint8_t v_kind_boxed_1781_; lean_object* v_res_1782_; 
v_bi_boxed_1780_ = lean_unbox(v_bi_1770_);
v_kind_boxed_1781_ = lean_unbox(v_kind_1773_);
v_res_1782_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__10_spec__12(v_00_u03b1_1768_, v_name_1769_, v_bi_boxed_1780_, v_type_1771_, v_k_1772_, v_kind_boxed_1781_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(lean_object* v_00_u03b1_1783_, lean_object* v_name_1784_, lean_object* v_type_1785_, lean_object* v_val_1786_, lean_object* v_k_1787_, uint8_t v_nondep_1788_, uint8_t v_kind_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___redArg(v_name_1784_, v_type_1785_, v_val_1786_, v_k_1787_, v_nondep_1788_, v_kind_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_name_1798_, lean_object* v_type_1799_, lean_object* v_val_1800_, lean_object* v_k_1801_, lean_object* v_nondep_1802_, lean_object* v_kind_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_nondep_boxed_1810_; uint8_t v_kind_boxed_1811_; lean_object* v_res_1812_; 
v_nondep_boxed_1810_ = lean_unbox(v_nondep_1802_);
v_kind_boxed_1811_ = lean_unbox(v_kind_1803_);
v_res_1812_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__12_spec__15(v_00_u03b1_1797_, v_name_1798_, v_type_1799_, v_val_1800_, v_k_1801_, v_nondep_boxed_1810_, v_kind_boxed_1811_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(lean_object* v_00_u03b1_1813_, lean_object* v_ref_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___redArg(v_ref_1814_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_ref_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14_spec__18(v_00_u03b1_1821_, v_ref_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(lean_object* v_00_u03b1_1829_, lean_object* v_x_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___redArg(v_x_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14___boxed(lean_object* v_00_u03b1_1838_, lean_object* v_x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__14(v_00_u03b1_1838_, v_x_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1847_, lean_object* v_m_1848_, lean_object* v_a_1849_, lean_object* v_b_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15___redArg(v_m_1848_, v_a_1849_, v_b_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(lean_object* v_00_u03b2_1852_, lean_object* v_a_1853_, lean_object* v_x_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___redArg(v_a_1853_, v_x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_00_u03b2_1856_, lean_object* v_a_1857_, lean_object* v_x_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__9_spec__10(v_00_u03b2_1856_, v_a_1857_, v_x_1858_);
lean_dec(v_x_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(lean_object* v_00_u03b2_1860_, lean_object* v_a_1861_, lean_object* v_x_1862_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___redArg(v_a_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20___boxed(lean_object* v_00_u03b2_1864_, lean_object* v_a_1865_, lean_object* v_x_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__20(v_00_u03b2_1864_, v_a_1865_, v_x_1866_);
lean_dec(v_x_1866_);
lean_dec_ref(v_a_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21(lean_object* v_00_u03b2_1869_, lean_object* v_data_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21___redArg(v_data_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22(lean_object* v_00_u03b2_1872_, lean_object* v_a_1873_, lean_object* v_b_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__22___redArg(v_a_1873_, v_b_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22(lean_object* v_00_u03b2_1877_, lean_object* v_i_1878_, lean_object* v_source_1879_, lean_object* v_target_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22___redArg(v_i_1878_, v_source_1879_, v_target_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23(lean_object* v_00_u03b2_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_WF_packCalls_spec__3_spec__4_spec__15_spec__21_spec__22_spec__23___redArg(v_x_1883_, v_x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName(lean_object* v_fixedParamPerms_1892_, lean_object* v_argsPacker_1893_, lean_object* v_preDefs_1894_){
_start:
{
uint8_t v___y_1896_; uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_1892_);
if (v___x_1916_ == 0)
{
v___y_1896_ = v___x_1916_;
goto v___jp_1895_;
}
else
{
uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_1893_);
v___y_1896_ = v___x_1917_;
goto v___jp_1895_;
}
v___jp_1895_:
{
if (v___y_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_1893_);
v___x_1899_ = lean_nat_dec_lt(v___x_1897_, v___x_1898_);
lean_dec(v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v_declName_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1900_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_array_get_borrowed(v___x_1900_, v_preDefs_1894_, v___x_1901_);
v_declName_1903_ = lean_ctor_get(v___x_1902_, 3);
v___x_1904_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__1));
lean_inc(v_declName_1903_);
v___x_1905_ = l_Lean_Name_append(v_declName_1903_, v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_declName_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1906_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_array_get_borrowed(v___x_1906_, v_preDefs_1894_, v___x_1907_);
v_declName_1909_ = lean_ctor_get(v___x_1908_, 3);
v___x_1910_ = ((lean_object*)(l_Lean_Elab_WF_mutualName___closed__3));
lean_inc(v_declName_1909_);
v___x_1911_ = l_Lean_Name_append(v_declName_1909_, v___x_1910_);
return v___x_1911_;
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_declName_1915_; 
v___x_1912_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_array_get_borrowed(v___x_1912_, v_preDefs_1894_, v___x_1913_);
v_declName_1915_ = lean_ctor_get(v___x_1914_, 3);
lean_inc(v_declName_1915_);
return v_declName_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mutualName___boxed(lean_object* v_fixedParamPerms_1918_, lean_object* v_argsPacker_1919_, lean_object* v_preDefs_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_1918_, v_argsPacker_1919_, v_preDefs_1920_);
lean_dec_ref(v_preDefs_1920_);
lean_dec_ref(v_argsPacker_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(lean_object* v_k_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
v___x_1929_ = lean_apply_6(v_k_1922_, v_b_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, lean_box(0));
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed(lean_object* v_k_1930_, lean_object* v_b_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0(v_k_1930_, v_b_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(lean_object* v_perm_1938_, lean_object* v_type_1939_, lean_object* v_k_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___f_1946_; lean_object* v___x_1947_; 
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1946_, 0, v_k_1940_);
v___x_1947_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1938_, v_type_1939_, v___f_1946_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
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
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1947_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1947_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg___boxed(lean_object* v_perm_1964_, lean_object* v_type_1965_, lean_object* v_k_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1964_, v_type_1965_, v_k_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(lean_object* v_00_u03b1_1973_, lean_object* v_perm_1974_, lean_object* v_type_1975_, lean_object* v_k_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v_perm_1974_, v_type_1975_, v_k_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_perm_1984_, lean_object* v_type_1985_, lean_object* v_k_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4(v_00_u03b1_1983_, v_perm_1984_, v_type_1985_, v_k_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(lean_object* v___x_1993_, lean_object* v_ys_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_bs_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_dec_ref(v_ys_1994_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_bs_1997_);
return v___x_2004_;
}
else
{
lean_object* v_v_2005_; lean_object* v_value_2006_; lean_object* v___x_2007_; lean_object* v_bs_x27_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_v_2005_ = lean_array_uget_borrowed(v_bs_1997_, v_i_1996_);
v_value_2006_ = lean_ctor_get(v_v_2005_, 7);
lean_inc_ref(v_value_2006_);
v___x_2007_ = lean_unsigned_to_nat(0u);
v_bs_x27_2008_ = lean_array_uset(v_bs_1997_, v_i_1996_, v___x_2007_);
v___x_2009_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2010_ = lean_usize_to_nat(v_i_1996_);
v___x_2011_ = lean_array_get_borrowed(v___x_2009_, v___x_1993_, v___x_2010_);
lean_dec(v___x_2010_);
lean_inc_ref(v_ys_1994_);
lean_inc(v___x_2011_);
v___x_2012_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2011_, v_value_2006_, v_ys_1994_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; size_t v___x_2014_; size_t v___x_2015_; lean_object* v___x_2016_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = ((size_t)1ULL);
v___x_2015_ = lean_usize_add(v_i_1996_, v___x_2014_);
v___x_2016_ = lean_array_uset(v_bs_x27_2008_, v_i_1996_, v_a_2013_);
v_i_1996_ = v___x_2015_;
v_bs_1997_ = v___x_2016_;
goto _start;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_bs_x27_2008_);
lean_dec_ref(v_ys_1994_);
v_a_2018_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2012_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2012_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg___boxed(lean_object* v___x_2026_, lean_object* v_ys_2027_, lean_object* v_sz_2028_, lean_object* v_i_2029_, lean_object* v_bs_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
size_t v_sz_boxed_2036_; size_t v_i_boxed_2037_; lean_object* v_res_2038_; 
v_sz_boxed_2036_ = lean_unbox_usize(v_sz_2028_);
lean_dec(v_sz_2028_);
v_i_boxed_2037_ = lean_unbox_usize(v_i_2029_);
lean_dec(v_i_2029_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2026_, v_ys_2027_, v_sz_boxed_2036_, v_i_boxed_2037_, v_bs_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec_ref(v___x_2026_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(lean_object* v___x_2039_, lean_object* v_ys_2040_, size_t v_sz_2041_, size_t v_i_2042_, lean_object* v_bs_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2042_, v_sz_2041_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
lean_dec_ref(v_ys_2040_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_bs_2043_);
return v___x_2050_;
}
else
{
lean_object* v_v_2051_; lean_object* v_type_2052_; lean_object* v___x_2053_; lean_object* v_bs_x27_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_v_2051_ = lean_array_uget_borrowed(v_bs_2043_, v_i_2042_);
v_type_2052_ = lean_ctor_get(v_v_2051_, 6);
lean_inc_ref(v_type_2052_);
v___x_2053_ = lean_unsigned_to_nat(0u);
v_bs_x27_2054_ = lean_array_uset(v_bs_2043_, v_i_2042_, v___x_2053_);
v___x_2055_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2056_ = lean_usize_to_nat(v_i_2042_);
v___x_2057_ = lean_array_get_borrowed(v___x_2055_, v___x_2039_, v___x_2056_);
lean_dec(v___x_2056_);
lean_inc_ref(v_ys_2040_);
lean_inc(v___x_2057_);
v___x_2058_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2057_, v_type_2052_, v_ys_2040_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2042_, v___x_2060_);
v___x_2062_ = lean_array_uset(v_bs_x27_2054_, v_i_2042_, v_a_2059_);
v_i_2042_ = v___x_2061_;
v_bs_2043_ = v___x_2062_;
goto _start;
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_bs_x27_2054_);
lean_dec_ref(v_ys_2040_);
v_a_2064_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2058_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2058_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg___boxed(lean_object* v___x_2072_, lean_object* v_ys_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_bs_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2072_, v_ys_2073_, v_sz_boxed_2082_, v_i_boxed_2083_, v_bs_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v___x_2072_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
if (lean_obj_tag(v_a_2085_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = l_List_reverse___redArg(v_a_2086_);
return v___x_2087_;
}
else
{
lean_object* v_head_2088_; lean_object* v_tail_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2098_; 
v_head_2088_ = lean_ctor_get(v_a_2085_, 0);
v_tail_2089_ = lean_ctor_get(v_a_2085_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2091_ = v_a_2085_;
v_isShared_2092_ = v_isSharedCheck_2098_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_tail_2089_);
lean_inc(v_head_2088_);
lean_dec(v_a_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2098_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = l_Lean_mkLevelParam(v_head_2088_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v_a_2086_);
lean_ctor_set(v___x_2091_, 0, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_a_2086_);
v___x_2095_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
v_a_2085_ = v_tail_2089_;
v_a_2086_ = v___x_2095_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(size_t v_sz_2099_, size_t v_i_2100_, lean_object* v_bs_2101_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_usize_dec_lt(v_i_2100_, v_sz_2099_);
if (v___x_2102_ == 0)
{
return v_bs_2101_;
}
else
{
lean_object* v_v_2103_; lean_object* v_declName_2104_; lean_object* v___x_2105_; lean_object* v_bs_x27_2106_; size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v_v_2103_ = lean_array_uget_borrowed(v_bs_2101_, v_i_2100_);
v_declName_2104_ = lean_ctor_get(v_v_2103_, 3);
lean_inc(v_declName_2104_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v_bs_x27_2106_ = lean_array_uset(v_bs_2101_, v_i_2100_, v___x_2105_);
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_add(v_i_2100_, v___x_2107_);
v___x_2109_ = lean_array_uset(v_bs_x27_2106_, v_i_2100_, v_declName_2104_);
v_i_2100_ = v___x_2108_;
v_bs_2101_ = v___x_2109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3___boxed(lean_object* v_sz_2111_, lean_object* v_i_2112_, lean_object* v_bs_2113_){
_start:
{
size_t v_sz_boxed_2114_; size_t v_i_boxed_2115_; lean_object* v_res_2116_; 
v_sz_boxed_2114_ = lean_unbox_usize(v_sz_2111_);
lean_dec(v_sz_2111_);
v_i_boxed_2115_ = lean_unbox_usize(v_i_2112_);
lean_dec(v_i_2112_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_boxed_2114_, v_i_boxed_2115_, v_bs_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0(lean_object* v_preDefs_2117_, lean_object* v_perms_2118_, lean_object* v_argsPacker_2119_, uint8_t v___x_2120_, lean_object* v_ref_2121_, uint8_t v_kind_2122_, lean_object* v_levelParams_2123_, lean_object* v_modifiers_2124_, lean_object* v_newFn_2125_, lean_object* v_binders_2126_, lean_object* v_numSectionVars_2127_, lean_object* v_value_2128_, lean_object* v_termination_2129_, lean_object* v_fixedParamPerms_2130_, lean_object* v_ys_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
size_t v_sz_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v_sz_2137_ = lean_array_size(v_preDefs_2117_);
v___x_2138_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_2117_);
lean_inc_ref(v_ys_2131_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v_perms_2118_, v_ys_2131_, v_sz_2137_, v___x_2138_, v_preDefs_2117_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
lean_inc_ref(v_preDefs_2117_);
lean_inc_ref(v_ys_2131_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v_perms_2118_, v_ys_2131_, v_sz_2137_, v___x_2138_, v_preDefs_2117_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2119_, v_a_2140_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v_a_2140_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; uint8_t v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = 1;
v___x_2146_ = 1;
v___x_2147_ = l_Lean_Meta_mkForallFVars(v_ys_2131_, v_a_2144_, v___x_2120_, v___x_2145_, v___x_2145_, v___x_2146_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc_n(v_a_2148_, 2);
lean_dec_ref_known(v___x_2147_, 1);
lean_inc_ref(v_termination_2129_);
lean_inc(v_numSectionVars_2127_);
lean_inc(v_binders_2126_);
lean_inc(v_newFn_2125_);
lean_inc_ref(v_modifiers_2124_);
lean_inc(v_levelParams_2123_);
lean_inc(v_ref_2121_);
v___x_2149_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2149_, 0, v_ref_2121_);
lean_ctor_set(v___x_2149_, 1, v_levelParams_2123_);
lean_ctor_set(v___x_2149_, 2, v_modifiers_2124_);
lean_ctor_set(v___x_2149_, 3, v_newFn_2125_);
lean_ctor_set(v___x_2149_, 4, v_binders_2126_);
lean_ctor_set(v___x_2149_, 5, v_numSectionVars_2127_);
lean_ctor_set(v___x_2149_, 6, v_a_2148_);
lean_ctor_set(v___x_2149_, 7, v_value_2128_);
lean_ctor_set(v___x_2149_, 8, v_termination_2129_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*9, v_kind_2122_);
v___x_2150_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2149_, v___y_2134_, v___y_2135_);
lean_dec_ref_known(v___x_2149_, 9);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v___x_2151_; 
lean_dec_ref_known(v___x_2150_, 1);
v___x_2151_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_2119_, v_a_2142_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v_a_2142_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2153_ = lean_box(0);
lean_inc(v_levelParams_2123_);
v___x_2154_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_2123_, v___x_2153_);
lean_inc(v_newFn_2125_);
v___x_2155_ = l_Lean_mkConst(v_newFn_2125_, v___x_2154_);
v___x_2156_ = l_Lean_mkAppN(v___x_2155_, v_ys_2131_);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__3(v_sz_2137_, v___x_2138_, v_preDefs_2117_);
v___x_2158_ = l_Lean_Elab_WF_packCalls(v_fixedParamPerms_2130_, v_argsPacker_2119_, v___x_2157_, v___x_2156_, v_a_2152_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2160_ = l_Lean_Meta_mkLambdaFVars(v_ys_2131_, v_a_2159_, v___x_2120_, v___x_2145_, v___x_2120_, v___x_2145_, v___x_2146_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec_ref(v_ys_2131_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2169_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2169_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2169_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2165_, 0, v_ref_2121_);
lean_ctor_set(v___x_2165_, 1, v_levelParams_2123_);
lean_ctor_set(v___x_2165_, 2, v_modifiers_2124_);
lean_ctor_set(v___x_2165_, 3, v_newFn_2125_);
lean_ctor_set(v___x_2165_, 4, v_binders_2126_);
lean_ctor_set(v___x_2165_, 5, v_numSectionVars_2127_);
lean_ctor_set(v___x_2165_, 6, v_a_2148_);
lean_ctor_set(v___x_2165_, 7, v_a_2161_);
lean_ctor_set(v___x_2165_, 8, v_termination_2129_);
lean_ctor_set_uint8(v___x_2165_, sizeof(void*)*9, v_kind_2122_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2148_);
lean_dec_ref(v_termination_2129_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
v_a_2170_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2160_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2160_);
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
lean_dec(v_a_2148_);
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_termination_2129_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
v_a_2178_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2158_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2158_);
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
lean_dec(v_a_2148_);
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_fixedParamPerms_2130_);
lean_dec_ref(v_termination_2129_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
lean_dec_ref(v_argsPacker_2119_);
lean_dec_ref(v_preDefs_2117_);
v_a_2186_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2151_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2151_);
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
lean_dec(v_a_2148_);
lean_dec(v_a_2142_);
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_fixedParamPerms_2130_);
lean_dec_ref(v_termination_2129_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
lean_dec_ref(v_argsPacker_2119_);
lean_dec_ref(v_preDefs_2117_);
v_a_2194_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2150_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2150_);
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
lean_dec(v_a_2142_);
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_fixedParamPerms_2130_);
lean_dec_ref(v_termination_2129_);
lean_dec_ref(v_value_2128_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
lean_dec_ref(v_argsPacker_2119_);
lean_dec_ref(v_preDefs_2117_);
v_a_2202_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2147_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2147_);
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
lean_dec(v_a_2142_);
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_fixedParamPerms_2130_);
lean_dec_ref(v_termination_2129_);
lean_dec_ref(v_value_2128_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
lean_dec_ref(v_argsPacker_2119_);
lean_dec_ref(v_preDefs_2117_);
v_a_2210_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2143_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2143_);
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
lean_dec(v_a_2140_);
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_fixedParamPerms_2130_);
lean_dec_ref(v_termination_2129_);
lean_dec_ref(v_value_2128_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
lean_dec_ref(v_argsPacker_2119_);
lean_dec_ref(v_preDefs_2117_);
v_a_2218_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2141_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2141_);
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
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_ys_2131_);
lean_dec_ref(v_fixedParamPerms_2130_);
lean_dec_ref(v_termination_2129_);
lean_dec_ref(v_value_2128_);
lean_dec(v_numSectionVars_2127_);
lean_dec(v_binders_2126_);
lean_dec(v_newFn_2125_);
lean_dec_ref(v_modifiers_2124_);
lean_dec(v_levelParams_2123_);
lean_dec(v_ref_2121_);
lean_dec_ref(v_argsPacker_2119_);
lean_dec_ref(v_preDefs_2117_);
v_a_2226_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2139_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2139_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___lam__0___boxed(lean_object** _args){
lean_object* v_preDefs_2234_ = _args[0];
lean_object* v_perms_2235_ = _args[1];
lean_object* v_argsPacker_2236_ = _args[2];
lean_object* v___x_2237_ = _args[3];
lean_object* v_ref_2238_ = _args[4];
lean_object* v_kind_2239_ = _args[5];
lean_object* v_levelParams_2240_ = _args[6];
lean_object* v_modifiers_2241_ = _args[7];
lean_object* v_newFn_2242_ = _args[8];
lean_object* v_binders_2243_ = _args[9];
lean_object* v_numSectionVars_2244_ = _args[10];
lean_object* v_value_2245_ = _args[11];
lean_object* v_termination_2246_ = _args[12];
lean_object* v_fixedParamPerms_2247_ = _args[13];
lean_object* v_ys_2248_ = _args[14];
lean_object* v___y_2249_ = _args[15];
lean_object* v___y_2250_ = _args[16];
lean_object* v___y_2251_ = _args[17];
lean_object* v___y_2252_ = _args[18];
lean_object* v___y_2253_ = _args[19];
_start:
{
uint8_t v___x_2529__boxed_2254_; uint8_t v_kind_boxed_2255_; lean_object* v_res_2256_; 
v___x_2529__boxed_2254_ = lean_unbox(v___x_2237_);
v_kind_boxed_2255_ = lean_unbox(v_kind_2239_);
v_res_2256_ = l_Lean_Elab_WF_packMutual___lam__0(v_preDefs_2234_, v_perms_2235_, v_argsPacker_2236_, v___x_2529__boxed_2254_, v_ref_2238_, v_kind_boxed_2255_, v_levelParams_2240_, v_modifiers_2241_, v_newFn_2242_, v_binders_2243_, v_numSectionVars_2244_, v_value_2245_, v_termination_2246_, v_fixedParamPerms_2247_, v_ys_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_perms_2235_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual(lean_object* v_fixedParamPerms_2257_, lean_object* v_argsPacker_2258_, lean_object* v_preDefs_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v_ref_2268_; uint8_t v_kind_2269_; lean_object* v_levelParams_2270_; lean_object* v_modifiers_2271_; lean_object* v_declName_2272_; lean_object* v_binders_2273_; lean_object* v_numSectionVars_2274_; lean_object* v_type_2275_; lean_object* v_value_2276_; lean_object* v_termination_2277_; lean_object* v_newFn_2278_; uint8_t v___x_2279_; 
v___x_2265_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = lean_array_get_borrowed(v___x_2265_, v_preDefs_2259_, v___x_2266_);
v_ref_2268_ = lean_ctor_get(v___x_2267_, 0);
v_kind_2269_ = lean_ctor_get_uint8(v___x_2267_, sizeof(void*)*9);
v_levelParams_2270_ = lean_ctor_get(v___x_2267_, 1);
v_modifiers_2271_ = lean_ctor_get(v___x_2267_, 2);
v_declName_2272_ = lean_ctor_get(v___x_2267_, 3);
v_binders_2273_ = lean_ctor_get(v___x_2267_, 4);
v_numSectionVars_2274_ = lean_ctor_get(v___x_2267_, 5);
v_type_2275_ = lean_ctor_get(v___x_2267_, 6);
v_value_2276_ = lean_ctor_get(v___x_2267_, 7);
v_termination_2277_ = lean_ctor_get(v___x_2267_, 8);
lean_inc_ref(v_fixedParamPerms_2257_);
v_newFn_2278_ = l_Lean_Elab_WF_mutualName(v_fixedParamPerms_2257_, v_argsPacker_2258_, v_preDefs_2259_);
v___x_2279_ = lean_name_eq(v_newFn_2278_, v_declName_2272_);
if (v___x_2279_ == 0)
{
lean_object* v_perms_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_inc_ref(v_termination_2277_);
lean_inc_ref(v_value_2276_);
lean_inc_ref(v_type_2275_);
lean_inc(v_numSectionVars_2274_);
lean_inc(v_binders_2273_);
lean_inc_ref(v_modifiers_2271_);
lean_inc(v_levelParams_2270_);
lean_inc(v_ref_2268_);
v_perms_2280_ = lean_ctor_get(v_fixedParamPerms_2257_, 1);
lean_inc_ref_n(v_perms_2280_, 2);
v___x_2281_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2282_ = lean_box(v___x_2279_);
v___x_2283_ = lean_box(v_kind_2269_);
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_packMutual___lam__0___boxed), 20, 14);
lean_closure_set(v___f_2284_, 0, v_preDefs_2259_);
lean_closure_set(v___f_2284_, 1, v_perms_2280_);
lean_closure_set(v___f_2284_, 2, v_argsPacker_2258_);
lean_closure_set(v___f_2284_, 3, v___x_2282_);
lean_closure_set(v___f_2284_, 4, v_ref_2268_);
lean_closure_set(v___f_2284_, 5, v___x_2283_);
lean_closure_set(v___f_2284_, 6, v_levelParams_2270_);
lean_closure_set(v___f_2284_, 7, v_modifiers_2271_);
lean_closure_set(v___f_2284_, 8, v_newFn_2278_);
lean_closure_set(v___f_2284_, 9, v_binders_2273_);
lean_closure_set(v___f_2284_, 10, v_numSectionVars_2274_);
lean_closure_set(v___f_2284_, 11, v_value_2276_);
lean_closure_set(v___f_2284_, 12, v_termination_2277_);
lean_closure_set(v___f_2284_, 13, v_fixedParamPerms_2257_);
v___x_2285_ = lean_array_get(v___x_2281_, v_perms_2280_, v___x_2266_);
lean_dec_ref(v_perms_2280_);
v___x_2286_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_WF_packMutual_spec__4___redArg(v___x_2285_, v_type_2275_, v___f_2284_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
return v___x_2286_;
}
else
{
lean_object* v___x_2287_; 
lean_inc(v___x_2267_);
lean_dec(v_newFn_2278_);
lean_dec_ref(v_preDefs_2259_);
lean_dec_ref(v_argsPacker_2258_);
lean_dec_ref(v_fixedParamPerms_2257_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2267_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_packMutual___boxed(lean_object* v_fixedParamPerms_2288_, lean_object* v_argsPacker_2289_, lean_object* v_preDefs_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Elab_WF_packMutual(v_fixedParamPerms_2288_, v_argsPacker_2289_, v_preDefs_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(lean_object* v___x_2297_, lean_object* v_ys_2298_, lean_object* v_as_2299_, size_t v_sz_2300_, size_t v_i_2301_, lean_object* v_bs_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___redArg(v___x_2297_, v_ys_2298_, v_sz_2300_, v_i_2301_, v_bs_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0___boxed(lean_object* v___x_2309_, lean_object* v_ys_2310_, lean_object* v_as_2311_, lean_object* v_sz_2312_, lean_object* v_i_2313_, lean_object* v_bs_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
size_t v_sz_boxed_2320_; size_t v_i_boxed_2321_; lean_object* v_res_2322_; 
v_sz_boxed_2320_ = lean_unbox_usize(v_sz_2312_);
lean_dec(v_sz_2312_);
v_i_boxed_2321_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_res_2322_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__0(v___x_2309_, v_ys_2310_, v_as_2311_, v_sz_boxed_2320_, v_i_boxed_2321_, v_bs_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_as_2311_);
lean_dec_ref(v___x_2309_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(lean_object* v___x_2323_, lean_object* v_ys_2324_, lean_object* v_as_2325_, size_t v_sz_2326_, size_t v_i_2327_, lean_object* v_bs_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___redArg(v___x_2323_, v_ys_2324_, v_sz_2326_, v_i_2327_, v_bs_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1___boxed(lean_object* v___x_2335_, lean_object* v_ys_2336_, lean_object* v_as_2337_, lean_object* v_sz_2338_, lean_object* v_i_2339_, lean_object* v_bs_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
size_t v_sz_boxed_2346_; size_t v_i_boxed_2347_; lean_object* v_res_2348_; 
v_sz_boxed_2346_ = lean_unbox_usize(v_sz_2338_);
lean_dec(v_sz_2338_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_packMutual_spec__1(v___x_2335_, v_ys_2336_, v_as_2337_, v_sz_boxed_2346_, v_i_boxed_2347_, v_bs_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_as_2337_);
lean_dec_ref(v___x_2335_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(lean_object* v_e_2349_, lean_object* v_k_2350_, uint8_t v_cleanupAnnotations_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___f_2357_; uint8_t v___x_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___f_2357_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2357_, 0, v_k_2350_);
v___x_2358_ = 1;
v___x_2359_ = 0;
v___x_2360_ = lean_box(0);
v___x_2361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2349_, v___x_2358_, v___x_2359_, v___x_2358_, v___x_2359_, v___x_2360_, v___f_2357_, v_cleanupAnnotations_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
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
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2361_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2361_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg___boxed(lean_object* v_e_2378_, lean_object* v_k_2379_, lean_object* v_cleanupAnnotations_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2386_; lean_object* v_res_2387_; 
v_cleanupAnnotations_boxed_2386_ = lean_unbox(v_cleanupAnnotations_2380_);
v_res_2387_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2378_, v_k_2379_, v_cleanupAnnotations_boxed_2386_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(lean_object* v_00_u03b1_2388_, lean_object* v_e_2389_, lean_object* v_k_2390_, uint8_t v_cleanupAnnotations_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_e_2389_, v_k_2390_, v_cleanupAnnotations_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___boxed(lean_object* v_00_u03b1_2398_, lean_object* v_e_2399_, lean_object* v_k_2400_, lean_object* v_cleanupAnnotations_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2407_; lean_object* v_res_2408_; 
v_cleanupAnnotations_boxed_2407_ = lean_unbox(v_cleanupAnnotations_2401_);
v_res_2408_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0(v_00_u03b1_2398_, v_e_2399_, v_k_2400_, v_cleanupAnnotations_boxed_2407_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(lean_object* v_msg_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___f_2415_; lean_object* v___x_1717__overap_2416_; lean_object* v___x_2417_; 
v___f_2415_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1717__overap_2416_ = lean_panic_fn_borrowed(v___f_2415_, v_msg_2409_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
v___x_2417_ = lean_apply_5(v___x_1717__overap_2416_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1___boxed(lean_object* v_msg_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v_msg_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0(lean_object* v_xs_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_array_get_size(v_xs_2425_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__0___boxed(lean_object* v_xs_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Elab_WF_varyingVarNames___lam__0(v_xs_2434_, v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_x_2435_);
lean_dec_ref(v_xs_2434_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(lean_object* v_as_2442_, size_t v_sz_2443_, size_t v_i_2444_, lean_object* v_b_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_a_2451_; uint8_t v___x_2455_; 
v___x_2455_ = lean_usize_dec_lt(v_i_2444_, v_sz_2443_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_b_2445_);
return v___x_2456_;
}
else
{
lean_object* v_snd_2457_; lean_object* v_fst_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2502_; 
v_snd_2457_ = lean_ctor_get(v_b_2445_, 1);
v_fst_2458_ = lean_ctor_get(v_b_2445_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_b_2445_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2460_ = v_b_2445_;
v_isShared_2461_ = v_isSharedCheck_2502_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snd_2457_);
lean_inc(v_fst_2458_);
lean_dec(v_b_2445_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2502_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_array_2462_; lean_object* v_start_2463_; lean_object* v_stop_2464_; uint8_t v___x_2465_; 
v_array_2462_ = lean_ctor_get(v_snd_2457_, 0);
v_start_2463_ = lean_ctor_get(v_snd_2457_, 1);
v_stop_2464_ = lean_ctor_get(v_snd_2457_, 2);
v___x_2465_ = lean_nat_dec_lt(v_start_2463_, v_stop_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2467_; 
if (v_isShared_2461_ == 0)
{
v___x_2467_ = v___x_2460_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_fst_2458_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_snd_2457_);
v___x_2467_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
else
{
lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2498_; 
lean_inc(v_stop_2464_);
lean_inc(v_start_2463_);
lean_inc_ref(v_array_2462_);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_snd_2457_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; 
v_unused_2499_ = lean_ctor_get(v_snd_2457_, 2);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_snd_2457_, 1);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_snd_2457_, 0);
lean_dec(v_unused_2501_);
v___x_2471_ = v_snd_2457_;
v_isShared_2472_ = v_isSharedCheck_2498_;
goto v_resetjp_2470_;
}
else
{
lean_dec(v_snd_2457_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2498_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2473_ = lean_array_fget(v_array_2462_, v_start_2463_);
v___x_2474_ = lean_unsigned_to_nat(1u);
v___x_2475_ = lean_nat_add(v_start_2463_, v___x_2474_);
lean_dec(v_start_2463_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2475_);
v___x_2477_ = v___x_2471_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_array_2462_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_stop_2464_);
v___x_2477_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_a_2478_ = lean_array_uget_borrowed(v_as_2442_, v_i_2444_);
v___x_2479_ = l_Lean_Expr_fvarId_x21(v_a_2478_);
v___x_2480_ = l_Lean_FVarId_getUserName___redArg(v___x_2479_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___x_2482_ = lean_array_push(v_fst_2458_, v_a_2481_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2477_);
lean_ctor_set(v___x_2460_, 0, v___x_2482_);
v___x_2484_ = v___x_2460_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2477_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
v_a_2451_ = v___x_2484_;
goto v___jp_2450_;
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v___x_2477_);
lean_del_object(v___x_2460_);
lean_dec(v_fst_2458_);
v_a_2486_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2480_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2480_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v___x_2495_; 
lean_dec_ref_known(v___x_2473_, 1);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2477_);
v___x_2495_ = v___x_2460_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_fst_2458_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2477_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
v_a_2451_ = v___x_2495_;
goto v___jp_2450_;
}
}
}
}
}
}
}
v___jp_2450_:
{
size_t v___x_2452_; size_t v___x_2453_; 
v___x_2452_ = ((size_t)1ULL);
v___x_2453_ = lean_usize_add(v_i_2444_, v___x_2452_);
v_i_2444_ = v___x_2453_;
v_b_2445_ = v_a_2451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg___boxed(lean_object* v_as_2503_, lean_object* v_sz_2504_, lean_object* v_i_2505_, lean_object* v_b_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
size_t v_sz_boxed_2511_; size_t v_i_boxed_2512_; lean_object* v_res_2513_; 
v_sz_boxed_2511_ = lean_unbox_usize(v_sz_2504_);
lean_dec(v_sz_2504_);
v_i_boxed_2512_ = lean_unbox_usize(v_i_2505_);
lean_dec(v_i_2505_);
v_res_2513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2503_, v_sz_boxed_2511_, v_i_boxed_2512_, v_b_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v_as_2503_);
return v_res_2513_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2516_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__1));
v___x_2517_ = lean_unsigned_to_nat(4u);
v___x_2518_ = lean_unsigned_to_nat(119u);
v___x_2519_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2520_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2521_ = l_mkPanicMessageWithDecl(v___x_2520_, v___x_2519_, v___x_2518_, v___x_2517_, v___x_2516_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2523_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__3));
v___x_2524_ = lean_unsigned_to_nat(4u);
v___x_2525_ = lean_unsigned_to_nat(120u);
v___x_2526_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__0));
v___x_2527_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2528_ = l_mkPanicMessageWithDecl(v___x_2527_, v___x_2526_, v___x_2525_, v___x_2524_, v___x_2523_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1(lean_object* v_a_2531_, lean_object* v_fixedParamPerms_2532_, lean_object* v_preDefIdx_2533_, lean_object* v_xs_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = lean_array_get_size(v_xs_2534_);
v___x_2542_ = lean_nat_dec_eq(v___x_2541_, v_a_2531_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__2);
v___x_2544_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2543_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2544_;
}
else
{
lean_object* v_perms_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_perms_2545_ = lean_ctor_get(v_fixedParamPerms_2532_, 1);
v___x_2546_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2547_ = lean_array_get_borrowed(v___x_2546_, v_perms_2545_, v_preDefIdx_2533_);
v___x_2548_ = lean_array_get_size(v___x_2547_);
v___x_2549_ = lean_nat_dec_eq(v___x_2548_, v_a_2531_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_obj_once(&l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4, &l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4_once, _init_l_Lean_Elab_WF_varyingVarNames___lam__1___closed__4);
v___x_2551_ = l_panic___at___00Lean_Elab_WF_varyingVarNames_spec__1(v___x_2550_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; size_t v_sz_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___lam__1___closed__5));
lean_inc(v___x_2547_);
v___x_2554_ = l_Array_toSubarray___redArg(v___x_2547_, v___x_2552_, v___x_2548_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v_sz_2556_ = lean_array_size(v_xs_2534_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_xs_2534_, v_sz_2556_, v___x_2557_, v___x_2555_, v___y_2536_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2567_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_fst_2563_; lean_object* v___x_2565_; 
v_fst_2563_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_fst_2563_);
lean_dec(v_a_2559_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v_fst_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_fst_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2558_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2558_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___lam__1___boxed(lean_object* v_a_2576_, lean_object* v_fixedParamPerms_2577_, lean_object* v_preDefIdx_2578_, lean_object* v_xs_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Elab_WF_varyingVarNames___lam__1(v_a_2576_, v_fixedParamPerms_2577_, v_preDefIdx_2578_, v_xs_2579_, v_x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v_x_2580_);
lean_dec_ref(v_xs_2579_);
lean_dec(v_preDefIdx_2578_);
lean_dec_ref(v_fixedParamPerms_2577_);
lean_dec(v_a_2576_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object* v_fixedParamPerms_2588_, lean_object* v_preDefIdx_2589_, lean_object* v_preDef_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_type_2596_; lean_object* v_value_2597_; lean_object* v___f_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; 
v_type_2596_ = lean_ctor_get(v_preDef_2590_, 6);
lean_inc_ref(v_type_2596_);
v_value_2597_ = lean_ctor_get(v_preDef_2590_, 7);
lean_inc_ref(v_value_2597_);
lean_dec_ref(v_preDef_2590_);
v___f_2598_ = ((lean_object*)(l_Lean_Elab_WF_varyingVarNames___closed__0));
v___x_2599_ = 0;
v___x_2600_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_varyingVarNames_spec__0___redArg(v_value_2597_, v___f_2598_, v___x_2599_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc_n(v_a_2601_, 2);
lean_dec_ref_known(v___x_2600_, 1);
v___f_2602_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_varyingVarNames___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2602_, 0, v_a_2601_);
lean_closure_set(v___f_2602_, 1, v_fixedParamPerms_2588_);
lean_closure_set(v___f_2602_, 2, v_preDefIdx_2589_);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v_a_2601_);
v___x_2604_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2596_, v___x_2603_, v___f_2602_, v___x_2599_, v___x_2599_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
return v___x_2604_;
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_type_2596_);
lean_dec(v_preDefIdx_2589_);
lean_dec_ref(v_fixedParamPerms_2588_);
v_a_2605_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2600_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2600_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_varyingVarNames___boxed(lean_object* v_fixedParamPerms_2613_, lean_object* v_preDefIdx_2614_, lean_object* v_preDef_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_Elab_WF_varyingVarNames(v_fixedParamPerms_2613_, v_preDefIdx_2614_, v_preDef_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(lean_object* v_as_2622_, size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___redArg(v_as_2622_, v_sz_2623_, v_i_2624_, v_b_2625_, v___y_2626_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2___boxed(lean_object* v_as_2632_, lean_object* v_sz_2633_, lean_object* v_i_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
size_t v_sz_boxed_2641_; size_t v_i_boxed_2642_; lean_object* v_res_2643_; 
v_sz_boxed_2641_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2642_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_varyingVarNames_spec__2(v_as_2632_, v_sz_boxed_2641_, v_i_boxed_2642_, v_b_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v_as_2632_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_1720__overap_2651_; lean_object* v___x_2652_; 
v___f_2650_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_packCalls_spec__1___closed__0));
v___x_1720__overap_2651_ = lean_panic_fn_borrowed(v___f_2650_, v_msg_2644_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2645_);
v___x_2652_ = lean_apply_5(v___x_1720__overap_2651_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, lean_box(0));
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0___boxed(lean_object* v_msg_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v_msg_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2659_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2660_; double v___x_2661_; 
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = lean_float_of_nat(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(lean_object* v_cls_2665_, lean_object* v_msg_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_ref_2672_; lean_object* v___x_2673_; lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2718_; 
v_ref_2672_ = lean_ctor_get(v___y_2669_, 5);
v___x_2673_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_WF_withAppN_spec__0_spec__0(v_msg_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2718_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2718_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v_traceState_2679_; lean_object* v_env_2680_; lean_object* v_nextMacroScope_2681_; lean_object* v_ngen_2682_; lean_object* v_auxDeclNGen_2683_; lean_object* v_cache_2684_; lean_object* v_messages_2685_; lean_object* v_infoState_2686_; lean_object* v_snapshotTasks_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2717_; 
v___x_2678_ = lean_st_ref_take(v___y_2670_);
v_traceState_2679_ = lean_ctor_get(v___x_2678_, 4);
v_env_2680_ = lean_ctor_get(v___x_2678_, 0);
v_nextMacroScope_2681_ = lean_ctor_get(v___x_2678_, 1);
v_ngen_2682_ = lean_ctor_get(v___x_2678_, 2);
v_auxDeclNGen_2683_ = lean_ctor_get(v___x_2678_, 3);
v_cache_2684_ = lean_ctor_get(v___x_2678_, 5);
v_messages_2685_ = lean_ctor_get(v___x_2678_, 6);
v_infoState_2686_ = lean_ctor_get(v___x_2678_, 7);
v_snapshotTasks_2687_ = lean_ctor_get(v___x_2678_, 8);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2689_ = v___x_2678_;
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snapshotTasks_2687_);
lean_inc(v_infoState_2686_);
lean_inc(v_messages_2685_);
lean_inc(v_cache_2684_);
lean_inc(v_traceState_2679_);
lean_inc(v_auxDeclNGen_2683_);
lean_inc(v_ngen_2682_);
lean_inc(v_nextMacroScope_2681_);
lean_inc(v_env_2680_);
lean_dec(v___x_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
uint64_t v_tid_2691_; lean_object* v_traces_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2716_; 
v_tid_2691_ = lean_ctor_get_uint64(v_traceState_2679_, sizeof(void*)*1);
v_traces_2692_ = lean_ctor_get(v_traceState_2679_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_traceState_2679_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2694_ = v_traceState_2679_;
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_traces_2692_);
lean_dec(v_traceState_2679_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; double v___x_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__0);
v___x_2698_ = 0;
v___x_2699_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__1));
v___x_2700_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2700_, 0, v_cls_2665_);
lean_ctor_set(v___x_2700_, 1, v___x_2696_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
lean_ctor_set_float(v___x_2700_, sizeof(void*)*3, v___x_2697_);
lean_ctor_set_float(v___x_2700_, sizeof(void*)*3 + 8, v___x_2697_);
lean_ctor_set_uint8(v___x_2700_, sizeof(void*)*3 + 16, v___x_2698_);
v___x_2701_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___closed__2));
v___x_2702_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v_a_2674_);
lean_ctor_set(v___x_2702_, 2, v___x_2701_);
lean_inc(v_ref_2672_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_ref_2672_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_PersistentArray_push___redArg(v_traces_2692_, v___x_2703_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2704_);
v___x_2706_ = v___x_2694_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2704_);
lean_ctor_set_uint64(v_reuseFailAlloc_2715_, sizeof(void*)*1, v_tid_2691_);
v___x_2706_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 4, v___x_2706_);
v___x_2708_ = v___x_2689_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_env_2680_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_nextMacroScope_2681_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v_ngen_2682_);
lean_ctor_set(v_reuseFailAlloc_2714_, 3, v_auxDeclNGen_2683_);
lean_ctor_set(v_reuseFailAlloc_2714_, 4, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2714_, 5, v_cache_2684_);
lean_ctor_set(v_reuseFailAlloc_2714_, 6, v_messages_2685_);
lean_ctor_set(v_reuseFailAlloc_2714_, 7, v_infoState_2686_);
lean_ctor_set(v_reuseFailAlloc_2714_, 8, v_snapshotTasks_2687_);
v___x_2708_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2709_ = lean_st_ref_set(v___y_2670_, v___x_2708_);
v___x_2710_ = lean_box(0);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2710_);
v___x_2712_ = v___x_2676_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1___boxed(lean_object* v_cls_2719_, lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v_cls_2719_, v_msg_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2726_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__1));
v___x_2730_ = lean_unsigned_to_nat(8u);
v___x_2731_ = lean_unsigned_to_nat(135u);
v___x_2732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__0));
v___x_2733_ = ((lean_object*)(l_Lean_Elab_WF_packCalls___lam__2___closed__0));
v___x_2734_ = l_mkPanicMessageWithDecl(v___x_2733_, v___x_2732_, v___x_2731_, v___x_2730_, v___x_2729_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(lean_object* v___x_2735_, lean_object* v_unaryPreDefNonRec_2736_, lean_object* v___x_2737_, lean_object* v_us_2738_, lean_object* v_argsPacker_2739_, lean_object* v___x_2740_, lean_object* v_params_2741_, lean_object* v_x_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = lean_array_get_size(v_params_2741_);
v___x_2749_ = lean_nat_dec_eq(v___x_2735_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec(v___x_2740_);
lean_dec(v_us_2738_);
lean_dec_ref(v_unaryPreDefNonRec_2736_);
v___x_2750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___closed__2);
v___x_2751_ = l_panic___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__0(v___x_2750_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2751_;
}
else
{
lean_object* v_declName_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_declName_2752_ = lean_ctor_get(v_unaryPreDefNonRec_2736_, 3);
lean_inc(v_declName_2752_);
lean_dec_ref(v_unaryPreDefNonRec_2736_);
v___x_2753_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2737_, v_params_2741_);
v___x_2754_ = l_Lean_mkConst(v_declName_2752_, v_us_2738_);
v___x_2755_ = l_Lean_mkAppN(v___x_2754_, v___x_2753_);
lean_dec_ref(v___x_2753_);
v___x_2756_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_2739_, v___x_2755_, v___x_2740_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2737_, v_params_2741_);
v___x_2759_ = l_Lean_Expr_beta(v_a_2757_, v___x_2758_);
v___x_2760_ = 0;
v___x_2761_ = 1;
v___x_2762_ = l_Lean_Meta_mkLambdaFVars(v_params_2741_, v___x_2759_, v___x_2760_, v___x_2749_, v___x_2760_, v___x_2749_, v___x_2761_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2762_;
}
else
{
return v___x_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed(lean_object* v___x_2763_, lean_object* v_unaryPreDefNonRec_2764_, lean_object* v___x_2765_, lean_object* v_us_2766_, lean_object* v_argsPacker_2767_, lean_object* v___x_2768_, lean_object* v_params_2769_, lean_object* v_x_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0(v___x_2763_, v_unaryPreDefNonRec_2764_, v___x_2765_, v_us_2766_, v_argsPacker_2767_, v___x_2768_, v_params_2769_, v_x_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v_x_2770_);
lean_dec_ref(v_params_2769_);
lean_dec_ref(v_argsPacker_2767_);
lean_dec_ref(v___x_2765_);
lean_dec(v___x_2763_);
return v_res_2776_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__5));
v___x_2789_ = l_Lean_Name_append(v___x_2788_, v___x_2787_);
return v___x_2789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__7));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(lean_object* v_fixedParamPerms_2793_, lean_object* v_unaryPreDefNonRec_2794_, lean_object* v_us_2795_, lean_object* v_argsPacker_2796_, size_t v_sz_2797_, size_t v_i_2798_, lean_object* v_bs_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_usize_dec_lt(v_i_2798_, v_sz_2797_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec_ref(v_argsPacker_2796_);
lean_dec(v_us_2795_);
lean_dec_ref(v_unaryPreDefNonRec_2794_);
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_bs_2799_);
return v___x_2806_;
}
else
{
lean_object* v_v_2807_; lean_object* v_perms_2808_; lean_object* v_ref_2809_; uint8_t v_kind_2810_; lean_object* v_levelParams_2811_; lean_object* v_modifiers_2812_; lean_object* v_declName_2813_; lean_object* v_binders_2814_; lean_object* v_numSectionVars_2815_; lean_object* v_type_2816_; lean_object* v_termination_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2868_; 
v_v_2807_ = lean_array_uget(v_bs_2799_, v_i_2798_);
v_perms_2808_ = lean_ctor_get(v_fixedParamPerms_2793_, 1);
v_ref_2809_ = lean_ctor_get(v_v_2807_, 0);
v_kind_2810_ = lean_ctor_get_uint8(v_v_2807_, sizeof(void*)*9);
v_levelParams_2811_ = lean_ctor_get(v_v_2807_, 1);
v_modifiers_2812_ = lean_ctor_get(v_v_2807_, 2);
v_declName_2813_ = lean_ctor_get(v_v_2807_, 3);
v_binders_2814_ = lean_ctor_get(v_v_2807_, 4);
v_numSectionVars_2815_ = lean_ctor_get(v_v_2807_, 5);
v_type_2816_ = lean_ctor_get(v_v_2807_, 6);
v_termination_2817_ = lean_ctor_get(v_v_2807_, 8);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_v_2807_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v_v_2807_, 7);
lean_dec(v_unused_2869_);
v___x_2819_ = v_v_2807_;
v_isShared_2820_ = v_isSharedCheck_2868_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_termination_2817_);
lean_inc(v_type_2816_);
lean_inc(v_numSectionVars_2815_);
lean_inc(v_binders_2814_);
lean_inc(v_declName_2813_);
lean_inc(v_modifiers_2812_);
lean_inc(v_levelParams_2811_);
lean_inc(v_ref_2809_);
lean_dec(v_v_2807_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2868_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v_bs_x27_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2821_ = lean_unsigned_to_nat(0u);
v_bs_x27_2822_ = lean_array_uset(v_bs_2799_, v_i_2798_, v___x_2821_);
v___x_2823_ = lean_obj_once(&l_Lean_Elab_WF_packCalls___lam__2___closed__4, &l_Lean_Elab_WF_packCalls___lam__2___closed__4_once, _init_l_Lean_Elab_WF_packCalls___lam__2___closed__4);
v___x_2824_ = lean_usize_to_nat(v_i_2798_);
v___x_2825_ = lean_array_get_borrowed(v___x_2823_, v_perms_2808_, v___x_2824_);
v___x_2826_ = lean_array_get_size(v___x_2825_);
lean_inc_ref(v_argsPacker_2796_);
lean_inc(v_us_2795_);
lean_inc(v___x_2825_);
lean_inc_ref(v_unaryPreDefNonRec_2794_);
v___f_2827_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_2827_, 0, v___x_2826_);
lean_closure_set(v___f_2827_, 1, v_unaryPreDefNonRec_2794_);
lean_closure_set(v___f_2827_, 2, v___x_2825_);
lean_closure_set(v___f_2827_, 3, v_us_2795_);
lean_closure_set(v___f_2827_, 4, v_argsPacker_2796_);
lean_closure_set(v___f_2827_, 5, v___x_2824_);
v___x_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
v___x_2829_ = 0;
lean_inc_ref(v_type_2816_);
v___x_2830_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_withAppN_spec__1___redArg(v_type_2816_, v___x_2828_, v___f_2827_, v___x_2829_, v___x_2829_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v_options_2840_; uint8_t v_hasTrace_2841_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v_options_2840_ = lean_ctor_get(v___y_2802_, 2);
v_hasTrace_2841_ = lean_ctor_get_uint8(v_options_2840_, sizeof(void*)*1);
if (v_hasTrace_2841_ == 0)
{
goto v___jp_2832_;
}
else
{
lean_object* v_inheritedTraceOptions_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_inheritedTraceOptions_2842_ = lean_ctor_get(v___y_2802_, 13);
v___x_2843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__3));
v___x_2844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__6);
v___x_2845_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2842_, v_options_2840_, v___x_2844_);
if (v___x_2845_ == 0)
{
goto v___jp_2832_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_inc(v_declName_2813_);
v___x_2846_ = l_Lean_MessageData_ofName(v_declName_2813_);
v___x_2847_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___closed__8);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
lean_inc(v_a_2831_);
v___x_2849_ = l_Lean_MessageData_ofExpr(v_a_2831_);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = l_Lean_addTrace___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__1(v___x_2843_, v___x_2850_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_dec_ref_known(v___x_2851_, 1);
goto v___jp_2832_;
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_a_2831_);
lean_dec_ref(v_bs_x27_2822_);
lean_del_object(v___x_2819_);
lean_dec_ref(v_termination_2817_);
lean_dec_ref(v_type_2816_);
lean_dec(v_numSectionVars_2815_);
lean_dec(v_binders_2814_);
lean_dec(v_declName_2813_);
lean_dec_ref(v_modifiers_2812_);
lean_dec(v_levelParams_2811_);
lean_dec(v_ref_2809_);
lean_dec_ref(v_argsPacker_2796_);
lean_dec(v_us_2795_);
lean_dec_ref(v_unaryPreDefNonRec_2794_);
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
v___jp_2832_:
{
lean_object* v___x_2834_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 7, v_a_2831_);
v___x_2834_ = v___x_2819_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_ref_2809_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_levelParams_2811_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_modifiers_2812_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_declName_2813_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_binders_2814_);
lean_ctor_set(v_reuseFailAlloc_2839_, 5, v_numSectionVars_2815_);
lean_ctor_set(v_reuseFailAlloc_2839_, 6, v_type_2816_);
lean_ctor_set(v_reuseFailAlloc_2839_, 7, v_a_2831_);
lean_ctor_set(v_reuseFailAlloc_2839_, 8, v_termination_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2839_, sizeof(void*)*9, v_kind_2810_);
v___x_2834_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
size_t v___x_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = ((size_t)1ULL);
v___x_2836_ = lean_usize_add(v_i_2798_, v___x_2835_);
v___x_2837_ = lean_array_uset(v_bs_x27_2822_, v_i_2798_, v___x_2834_);
v_i_2798_ = v___x_2836_;
v_bs_2799_ = v___x_2837_;
goto _start;
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_bs_x27_2822_);
lean_del_object(v___x_2819_);
lean_dec_ref(v_termination_2817_);
lean_dec_ref(v_type_2816_);
lean_dec(v_numSectionVars_2815_);
lean_dec(v_binders_2814_);
lean_dec(v_declName_2813_);
lean_dec_ref(v_modifiers_2812_);
lean_dec(v_levelParams_2811_);
lean_dec(v_ref_2809_);
lean_dec_ref(v_argsPacker_2796_);
lean_dec(v_us_2795_);
lean_dec_ref(v_unaryPreDefNonRec_2794_);
v_a_2860_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2830_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2830_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_2870_, lean_object* v_unaryPreDefNonRec_2871_, lean_object* v_us_2872_, lean_object* v_argsPacker_2873_, lean_object* v_sz_2874_, lean_object* v_i_2875_, lean_object* v_bs_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2874_);
lean_dec(v_sz_2874_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2875_);
lean_dec(v_i_2875_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2870_, v_unaryPreDefNonRec_2871_, v_us_2872_, v_argsPacker_2873_, v_sz_boxed_2882_, v_i_boxed_2883_, v_bs_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_fixedParamPerms_2870_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(lean_object* v_unaryPreDefNonRec_2885_, lean_object* v_preDefs_2886_, lean_object* v_fixedParamPerms_2887_, lean_object* v_us_2888_, lean_object* v_argsPacker_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Elab_addAsAxiom___redArg(v_unaryPreDefNonRec_2885_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2895_) == 0)
{
size_t v_sz_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
lean_dec_ref_known(v___x_2895_, 1);
v_sz_2896_ = lean_array_size(v_preDefs_2886_);
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_2887_, v_unaryPreDefNonRec_2885_, v_us_2888_, v_argsPacker_2889_, v_sz_2896_, v___x_2897_, v_preDefs_2886_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
return v___x_2898_;
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v_argsPacker_2889_);
lean_dec(v_us_2888_);
lean_dec_ref(v_preDefs_2886_);
lean_dec_ref(v_unaryPreDefNonRec_2885_);
v_a_2899_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2895_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2895_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed(lean_object* v_unaryPreDefNonRec_2907_, lean_object* v_preDefs_2908_, lean_object* v_fixedParamPerms_2909_, lean_object* v_us_2910_, lean_object* v_argsPacker_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0(v_unaryPreDefNonRec_2907_, v_preDefs_2908_, v_fixedParamPerms_2909_, v_us_2910_, v_argsPacker_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec_ref(v_fixedParamPerms_2909_);
return v_res_2917_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2918_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__0);
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
return v___x_2922_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__1);
v___x_2924_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
lean_ctor_set(v___x_2924_, 2, v___x_2923_);
lean_ctor_set(v___x_2924_, 3, v___x_2923_);
lean_ctor_set(v___x_2924_, 4, v___x_2923_);
lean_ctor_set(v___x_2924_, 5, v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(lean_object* v_env_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; lean_object* v_nextMacroScope_2930_; lean_object* v_ngen_2931_; lean_object* v_auxDeclNGen_2932_; lean_object* v_traceState_2933_; lean_object* v_messages_2934_; lean_object* v_infoState_2935_; lean_object* v_snapshotTasks_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2962_; 
v___x_2929_ = lean_st_ref_take(v___y_2927_);
v_nextMacroScope_2930_ = lean_ctor_get(v___x_2929_, 1);
v_ngen_2931_ = lean_ctor_get(v___x_2929_, 2);
v_auxDeclNGen_2932_ = lean_ctor_get(v___x_2929_, 3);
v_traceState_2933_ = lean_ctor_get(v___x_2929_, 4);
v_messages_2934_ = lean_ctor_get(v___x_2929_, 6);
v_infoState_2935_ = lean_ctor_get(v___x_2929_, 7);
v_snapshotTasks_2936_ = lean_ctor_get(v___x_2929_, 8);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2963_ = lean_ctor_get(v___x_2929_, 5);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v___x_2929_, 0);
lean_dec(v_unused_2964_);
v___x_2938_ = v___x_2929_;
v_isShared_2939_ = v_isSharedCheck_2962_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_snapshotTasks_2936_);
lean_inc(v_infoState_2935_);
lean_inc(v_messages_2934_);
lean_inc(v_traceState_2933_);
lean_inc(v_auxDeclNGen_2932_);
lean_inc(v_ngen_2931_);
lean_inc(v_nextMacroScope_2930_);
lean_dec(v___x_2929_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2962_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 5, v___x_2940_);
lean_ctor_set(v___x_2938_, 0, v_env_2925_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_env_2925_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_nextMacroScope_2930_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v_ngen_2931_);
lean_ctor_set(v_reuseFailAlloc_2961_, 3, v_auxDeclNGen_2932_);
lean_ctor_set(v_reuseFailAlloc_2961_, 4, v_traceState_2933_);
lean_ctor_set(v_reuseFailAlloc_2961_, 5, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2961_, 6, v_messages_2934_);
lean_ctor_set(v_reuseFailAlloc_2961_, 7, v_infoState_2935_);
lean_ctor_set(v_reuseFailAlloc_2961_, 8, v_snapshotTasks_2936_);
v___x_2942_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_mctx_2945_; lean_object* v_zetaDeltaFVarIds_2946_; lean_object* v_postponed_2947_; lean_object* v_diag_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2959_; 
v___x_2943_ = lean_st_ref_set(v___y_2927_, v___x_2942_);
v___x_2944_ = lean_st_ref_take(v___y_2926_);
v_mctx_2945_ = lean_ctor_get(v___x_2944_, 0);
v_zetaDeltaFVarIds_2946_ = lean_ctor_get(v___x_2944_, 2);
v_postponed_2947_ = lean_ctor_get(v___x_2944_, 3);
v_diag_2948_ = lean_ctor_get(v___x_2944_, 4);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v___x_2944_, 1);
lean_dec(v_unused_2960_);
v___x_2950_ = v___x_2944_;
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_diag_2948_);
lean_inc(v_postponed_2947_);
lean_inc(v_zetaDeltaFVarIds_2946_);
lean_inc(v_mctx_2945_);
lean_dec(v___x_2944_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2959_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_mctx_2945_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_zetaDeltaFVarIds_2946_);
lean_ctor_set(v_reuseFailAlloc_2958_, 3, v_postponed_2947_);
lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_diag_2948_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_st_ref_set(v___y_2926_, v___x_2954_);
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg___boxed(lean_object* v_env_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec(v___y_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(lean_object* v_env_2970_, lean_object* v_x_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v_env_2978_; lean_object* v_a_2980_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2977_ = lean_st_ref_get(v___y_2975_);
v_env_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_env_2978_);
lean_dec(v___x_2977_);
v___x_2990_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2970_, v___y_2973_, v___y_2975_);
lean_dec_ref(v___x_2990_);
lean_inc(v___y_2975_);
lean_inc_ref(v___y_2974_);
lean_inc(v___y_2973_);
lean_inc_ref(v___y_2972_);
v___x_2991_ = lean_apply_5(v_x_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, lean_box(0));
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2978_, v___y_2973_, v___y_2975_);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v___x_2993_, 0);
lean_dec(v_unused_3001_);
v___x_2995_ = v___x_2993_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v___x_2993_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v_a_2992_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2992_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_2991_, 1);
v_a_2980_ = v_a_3002_;
goto v___jp_2979_;
}
v___jp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v___x_2981_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_2978_, v___y_2973_, v___y_2975_);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2989_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 1);
lean_ctor_set(v___x_2983_, 0, v_a_2980_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2980_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg___boxed(lean_object* v_env_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3003_, v_x_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object* v_fixedParamPerms_3011_, lean_object* v_argsPacker_3012_, lean_object* v_preDefs_3013_, lean_object* v_unaryPreDefNonRec_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v___x_3020_; lean_object* v_levelParams_3021_; lean_object* v_env_3022_; lean_object* v___x_3023_; lean_object* v_us_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3020_ = lean_st_ref_get(v_a_3018_);
v_levelParams_3021_ = lean_ctor_get(v_unaryPreDefNonRec_3014_, 1);
v_env_3022_ = lean_ctor_get(v___x_3020_, 0);
lean_inc_ref(v_env_3022_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
lean_inc(v_levelParams_3021_);
v_us_3024_ = l_List_mapTR_loop___at___00Lean_Elab_WF_packMutual_spec__2(v_levelParams_3021_, v___x_3023_);
v___f_3025_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preDefsFromUnaryNonRec___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3025_, 0, v_unaryPreDefNonRec_3014_);
lean_closure_set(v___f_3025_, 1, v_preDefs_3013_);
lean_closure_set(v___f_3025_, 2, v_fixedParamPerms_3011_);
lean_closure_set(v___f_3025_, 3, v_us_3024_);
lean_closure_set(v___f_3025_, 4, v_argsPacker_3012_);
v___x_3026_ = l_Lean_Environment_unlockAsync(v_env_3022_);
v___x_3027_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v___x_3026_, v___f_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec___boxed(lean_object* v_fixedParamPerms_3028_, lean_object* v_argsPacker_3029_, lean_object* v_preDefs_3030_, lean_object* v_unaryPreDefNonRec_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fixedParamPerms_3028_, v_argsPacker_3029_, v_preDefs_3030_, v_unaryPreDefNonRec_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(lean_object* v_fixedParamPerms_3038_, lean_object* v_unaryPreDefNonRec_3039_, lean_object* v_us_3040_, lean_object* v_argsPacker_3041_, lean_object* v_as_3042_, size_t v_sz_3043_, size_t v_i_3044_, lean_object* v_bs_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___redArg(v_fixedParamPerms_3038_, v_unaryPreDefNonRec_3039_, v_us_3040_, v_argsPacker_3041_, v_sz_3043_, v_i_3044_, v_bs_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2___boxed(lean_object* v_fixedParamPerms_3052_, lean_object* v_unaryPreDefNonRec_3053_, lean_object* v_us_3054_, lean_object* v_argsPacker_3055_, lean_object* v_as_3056_, lean_object* v_sz_3057_, lean_object* v_i_3058_, lean_object* v_bs_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
size_t v_sz_boxed_3065_; size_t v_i_boxed_3066_; lean_object* v_res_3067_; 
v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3057_);
lean_dec(v_sz_3057_);
v_i_boxed_3066_ = lean_unbox_usize(v_i_3058_);
lean_dec(v_i_3058_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__2(v_fixedParamPerms_3052_, v_unaryPreDefNonRec_3053_, v_us_3054_, v_argsPacker_3055_, v_as_3056_, v_sz_boxed_3065_, v_i_boxed_3066_, v_bs_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v_as_3056_);
lean_dec_ref(v_fixedParamPerms_3052_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(lean_object* v_env_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___redArg(v_env_3068_, v___y_3070_, v___y_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3___boxed(lean_object* v_env_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3_spec__3(v_env_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(lean_object* v_00_u03b1_3082_, lean_object* v_env_3083_, lean_object* v_x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___redArg(v_env_3083_, v_x_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3___boxed(lean_object* v_00_u03b1_3091_, lean_object* v_env_3092_, lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_withEnv___at___00Lean_Elab_WF_preDefsFromUnaryNonRec_spec__3(v_00_u03b1_3091_, v_env_3092_, v_x_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3099_;
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
